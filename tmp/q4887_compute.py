from __future__ import annotations

from fractions import Fraction as FQ
from math import comb, gcd, isqrt
from pathlib import Path
from typing import List, Tuple, Optional

# This script is intentionally self-contained: no Sage/ore_algebra is required.
# It searches exact polynomial/rational Ore projectors from the centered-binomial
# Cooper trace W_n to the Problem 2.7 denominator q_n.

NTERMS = 180
PRIME_COUNT = 4
MAX_R = 8
MAX_D_DIRECT = 28
MAX_D_RATIONAL = 18
MAX_REC_ORDER = 9
MAX_REC_DEG = 22
HOLDOUT = 24

# ---------------------------------------------------------------------------
# Elementary primality / CRT / rational reconstruction
# ---------------------------------------------------------------------------

def is_probable_prime(n: int) -> bool:
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in small:
        if n % p == 0:
            return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    # Deterministic for <2^64.
    for a in [2, 325, 9375, 28178, 450775, 9780504, 1795265022]:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def previous_primes(start: int, count: int) -> List[int]:
    out = []
    x = start | 1
    while len(out) < count:
        if is_probable_prime(x):
            out.append(x)
        x -= 2
    return out

PRIMES = previous_primes((1 << 61) - 1, PRIME_COUNT)


def crt_pair(a: int, m: int, b: int, p: int) -> Tuple[int, int]:
    # m and p coprime; return x mod mp.
    t = ((b - a) % p) * pow(m % p, -1, p) % p
    x = a + m * t
    return x % (m * p), m * p


def rational_reconstruct(x: int, m: int) -> Optional[FQ]:
    x %= m
    bound = isqrt(m // 2)
    r0, r1 = m, x
    t0, t1 = 0, 1
    while abs(r1) > bound:
        if r1 == 0:
            return None
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        t0, t1 = t1, t0 - q * t1
    a, b = r1, t1
    if b == 0:
        return None
    if b < 0:
        a, b = -a, -b
    g = gcd(abs(a), b)
    a //= g
    b //= g
    if abs(a) > bound or b > bound:
        return None
    if (a - x * b) % m != 0:
        return None
    return FQ(a, b)

# ---------------------------------------------------------------------------
# Problem data over integers / rationals / finite fields
# ---------------------------------------------------------------------------

def A27(n: int) -> int:
    return 1024*(2*n+5)**4*(2*n+7)**3*(2*n+9)**3*(946*n*n+6407*n+10860)

def B27(n: int) -> int:
    return 128*(2*n+7)**3*(2*n+9)**3*(
        104060*n**6+1745370*n**5+12145238*n**4+44886481*n**3+
        92943995*n**2+102256019*n+46709052)

def C27(n: int) -> int:
    return 16*(n+3)**4*(2*n+9)**3*(
        3784*n**5+57792*n**4+351019*n**3+1059230*n**2+
        1587211*n+944620)

def D27(n: int) -> int:
    return (n+3)**4*(n+4)**6*(946*n*n+4515*n+5399)

Q_INIT = [
    FQ(-215040420000),
    FQ(-167282265043404, 905),
    FQ(-964185327658080, 6071),
]


def q_terms_exact(N: int) -> List[FQ]:
    q = Q_INIT[:]
    for n in range(2, N - 1):
        q.append(
            FQ(B27(n), A27(n))*q[n]
            - FQ(C27(n-1), A27(n-1))*q[n-1]
            + FQ(D27(n-2), A27(n-2))*q[n-2]
        )
    return q[:N]


def cooper_terms_exact(N: int) -> List[int]:
    T = [1, 4, 28]
    for n in range(2, N - 1):
        num = (
            2*(2*n+1)*(5*n*n+5*n+2)*T[n]
            - 8*n*(7*n*n+1)*T[n-1]
            + 22*n*(2*n-1)*(n-1)*T[n-2]
        )
        den = (n+1)**3
        assert num % den == 0
        T.append(num // den)
    return T[:N]


def W_terms_exact(N: int) -> List[FQ]:
    T = cooper_terms_exact(2*N)
    W = []
    for n in range(N):
        s = sum(comb(2*n, k)*(-2)**(2*n-k)*T[k] for k in range(2*n+1))
        W.append(FQ(s, 256**n))
    return W


def hA_terms_exact(N: int) -> List[FQ]:
    # h_n=(5/2)_n/n!, the simplest exact n^(3/2) twist.
    h = [FQ(1)]
    for n in range(N-1):
        h.append(h[-1] * FQ(2*n+5, 2*n+2))
    return h


def modfrac(x: FQ, p: int) -> int:
    return (x.numerator % p) * pow(x.denominator % p, -1, p) % p


def sequences_mod(p: int, N: int):
    # Cooper recurrence modulo p.
    T = [1 % p, 4 % p, 28 % p]
    for n in range(2, 2*N-1):
        num = (
            2*(2*n+1)*(5*n*n+5*n+2)*T[n]
            - 8*n*(7*n*n+1)*T[n-1]
            + 22*n*(2*n-1)*(n-1)*T[n-2]
        ) % p
        T.append(num * pow((n+1)**3 % p, -1, p) % p)
    inv256 = pow(256, -1, p)
    W = []
    scale = 1
    for n in range(N):
        s = 0
        for k in range(2*n+1):
            s = (s + comb(2*n, k) * pow(-2, 2*n-k, p) * T[k]) % p
        W.append(s * scale % p)
        scale = scale * inv256 % p

    q = [modfrac(x, p) for x in Q_INIT]
    for n in range(2, N-1):
        q.append((
            (B27(n) % p) * pow(A27(n) % p, -1, p) * q[n]
            - (C27(n-1) % p) * pow(A27(n-1) % p, -1, p) * q[n-1]
            + (D27(n-2) % p) * pow(A27(n-2) % p, -1, p) * q[n-2]
        ) % p)

    h = [1]
    for n in range(N-1):
        h.append(h[-1] * ((2*n+5) % p) * pow((2*n+2) % p, -1, p) % p)
    q_over_h = [q[n] * pow(h[n], -1, p) % p for n in range(N)]
    return W, q, h, q_over_h

# ---------------------------------------------------------------------------
# Modular linear algebra
# ---------------------------------------------------------------------------

def rref(A: List[List[int]], b: Optional[List[int]], p: int):
    M = [row[:] + ([] if b is None else [b[i] % p]) for i, row in enumerate(A)]
    nr = len(M)
    nc = len(A[0]) if A else 0
    pivots = []
    row = 0
    for col in range(nc):
        pivot = next((r for r in range(row, nr) if M[r][col] % p), None)
        if pivot is None:
            continue
        M[row], M[pivot] = M[pivot], M[row]
        inv = pow(M[row][col] % p, -1, p)
        M[row] = [(x * inv) % p for x in M[row]]
        for r in range(nr):
            if r != row and M[r][col] % p:
                c = M[r][col] % p
                M[r] = [(M[r][j] - c*M[row][j]) % p for j in range(len(M[r]))]
        pivots.append(col)
        row += 1
        if row == nr:
            break
    inconsistent = False
    if b is not None:
        for r in range(nr):
            if all(M[r][c] % p == 0 for c in range(nc)) and M[r][nc] % p:
                inconsistent = True
                break
    return M, pivots, inconsistent


def solve_unique(A: List[List[int]], b: List[int], p: int) -> Optional[List[int]]:
    M, pivots, bad = rref(A, b, p)
    nc = len(A[0])
    if bad or len(pivots) != nc:
        return None
    x = [0]*nc
    for r, c in enumerate(pivots):
        x[c] = M[r][nc] % p
    return x


def nullspace(A: List[List[int]], p: int) -> List[List[int]]:
    M, pivots, _ = rref(A, None, p)
    nc = len(A[0])
    free = [c for c in range(nc) if c not in pivots]
    out = []
    for f in free:
        v = [0]*nc
        v[f] = 1
        for r, c in enumerate(pivots):
            v[c] = (-M[r][f]) % p
        out.append(v)
    return out

# ---------------------------------------------------------------------------
# Relation searches
# ---------------------------------------------------------------------------

def direct_matrix(W: List[int], target: List[int], r: int, d: int, ns: List[int], p: int):
    A = []
    b = []
    for n in ns:
        A.append([pow(n, m, p)*W[n+j] % p for j in range(r+1) for m in range(d+1)])
        b.append(target[n] % p)
    return A, b


def verify_direct(sol, W, target, r, d, ns, p):
    for n in ns:
        val = 0
        z = 0
        for j in range(r+1):
            for m in range(d+1):
                val = (val + sol[z]*pow(n,m,p)*W[n+j]) % p
                z += 1
        if val != target[n] % p:
            return False
    return True


def search_direct(all_mod, target_key: str):
    p0 = PRIMES[0]
    W0, q0, h0, qh0 = all_mod[p0]
    target0 = q0 if target_key == 'q' else qh0
    results = []
    for r in range(MAX_R+1):
        for d in range(MAX_D_DIRECT+1):
            U = (r+1)*(d+1)
            total = NTERMS-r
            if U + HOLDOUT > total:
                continue
            train = list(range(U+4))
            hold = list(range(U+4, total))
            A,b = direct_matrix(W0,target0,r,d,train,p0)
            sol = solve_unique(A,b,p0)
            if sol is None or not verify_direct(sol,W0,target0,r,d,hold,p0):
                continue
            stable = True
            sols = {p0: sol}
            for p in PRIMES[1:]:
                W,q,h,qh = all_mod[p]
                target = q if target_key=='q' else qh
                A,b = direct_matrix(W,target,r,d,train,p)
                s = solve_unique(A,b,p)
                if s is None or not verify_direct(s,W,target,r,d,hold,p):
                    stable=False; break
                sols[p]=s
            if stable:
                results.append((r,d,sols))
                return results
    return results


def rational_relation_matrix(W, target, r, dp, de, ns, p):
    # Sum P_j(n) W_{n+j} - E(n) target_n = 0. Homogeneous.
    rows=[]
    for n in ns:
        row=[pow(n,m,p)*W[n+j]%p for j in range(r+1) for m in range(dp+1)]
        row += [(-pow(n,m,p)*target[n])%p for m in range(de+1)]
        rows.append(row)
    return rows


def verify_hom(v,W,target,r,dp,de,ns,p):
    for n in ns:
        z=0; val=0
        for j in range(r+1):
            for m in range(dp+1):
                val=(val+v[z]*pow(n,m,p)*W[n+j])%p; z+=1
        for m in range(de+1):
            val=(val-v[z]*pow(n,m,p)*target[n])%p; z+=1
        if val%p:
            return False
    return True


def search_rational(all_mod,target_key):
    p0=PRIMES[0]
    W0,q0,h0,qh0=all_mod[p0]
    target0=q0 if target_key=='q' else qh0
    candidates=[]
    # Search by total unknown count, then order.
    specs=[]
    for r in range(MAX_R+1):
        for dp in range(MAX_D_RATIONAL+1):
            for de in range(MAX_D_RATIONAL+1):
                U=(r+1)*(dp+1)+(de+1)
                if U+HOLDOUT <= NTERMS-r:
                    specs.append((U,r,dp,de))
    specs.sort()
    for U,r,dp,de in specs:
        train=list(range(U+3))
        hold=list(range(U+3,NTERMS-r))
        A=rational_relation_matrix(W0,target0,r,dp,de,train,p0)
        ns=nullspace(A,p0)
        good=[v for v in ns if any(v[(r+1)*(dp+1):]) and verify_hom(v,W0,target0,r,dp,de,hold,p0)]
        if len(good)!=1:
            continue
        v0=good[0]
        # normalize at last nonzero E coefficient if possible
        eoff=(r+1)*(dp+1)
        norm=max(i for i in range(eoff,len(v0)) if v0[i])
        v0=[x*pow(v0[norm],-1,p0)%p0 for x in v0]
        sols={p0:v0}
        stable=True
        for p in PRIMES[1:]:
            W,q,h,qh=all_mod[p]
            target=q if target_key=='q' else qh
            A=rational_relation_matrix(W,target,r,dp,de,train,p)
            ns2=nullspace(A,p)
            good2=[]
            for v in ns2:
                if norm < len(v) and v[norm] and any(v[eoff:]):
                    vn=[x*pow(v[norm],-1,p)%p for x in v]
                    if verify_hom(vn,W,target,r,dp,de,hold,p):
                        good2.append(vn)
            if len(good2)!=1:
                stable=False;break
            sols[p]=good2[0]
        if stable:
            candidates.append((r,dp,de,norm,sols))
            return candidates
    return candidates


def recurrence_matrix(W,r,d,ns,p):
    return [[pow(n,m,p)*W[n+j]%p for j in range(r+1) for m in range(d+1)] for n in ns]


def verify_rec(v,W,r,d,ns,p):
    for n in ns:
        z=0; val=0
        for j in range(r+1):
            for m in range(d+1):
                val=(val+v[z]*pow(n,m,p)*W[n+j])%p; z+=1
        if val%p:return False
    return True


def search_recurrence(all_mod):
    p0=PRIMES[0]; W0=all_mod[p0][0]
    specs=[]
    for r in range(1,MAX_REC_ORDER+1):
        for d in range(MAX_REC_DEG+1):
            U=(r+1)*(d+1)
            if U+HOLDOUT <= NTERMS-r:
                specs.append((U,r,d))
    specs.sort(key=lambda x:(x[1],x[2]))  # minimal order first, then degree
    for U,r,d in specs:
        train=list(range(U+3)); hold=list(range(U+3,NTERMS-r))
        ns=nullspace(recurrence_matrix(W0,r,d,train,p0),p0)
        good=[v for v in ns if verify_rec(v,W0,r,d,hold,p0)]
        if len(good)!=1:continue
        v0=good[0]
        norm=max(i for i,x in enumerate(v0) if x)
        v0=[x*pow(v0[norm],-1,p0)%p0 for x in v0]
        sols={p0:v0};stable=True
        for p in PRIMES[1:]:
            W=all_mod[p][0]
            ns2=nullspace(recurrence_matrix(W,r,d,train,p),p)
            good2=[]
            for v in ns2:
                if v[norm]:
                    vn=[x*pow(v[norm],-1,p)%p for x in v]
                    if verify_rec(vn,W,r,d,hold,p):good2.append(vn)
            if len(good2)!=1:stable=False;break
            sols[p]=good2[0]
        if stable:return (r,d,norm,sols)
    return None

# ---------------------------------------------------------------------------
# CRT reconstruction and exact verification
# ---------------------------------------------------------------------------

def reconstruct_vector(sols) -> Optional[List[FQ]]:
    ps=list(sols)
    L=len(sols[ps[0]])
    out=[]
    for i in range(L):
        x=sols[ps[0]][i]; m=ps[0]
        for p in ps[1:]:
            x,m=crt_pair(x,m,sols[p][i],p)
        rr=rational_reconstruct(x,m)
        if rr is None:
            return None
        out.append(rr)
    return out


def poly_to_str(cs: List[FQ], var='n'):
    parts=[]
    for m,c in enumerate(cs):
        if c==0:continue
        term=str(c)
        if m==1: term += f'*{var}'
        elif m>1: term += f'*{var}^{m}'
        parts.append(term)
    return ' + '.join(parts).replace('+ -','- ') if parts else '0'


def verify_direct_exact(vec,W,target,r,d):
    for n in range(len(target)-r):
        z=0; val=FQ(0)
        for j in range(r+1):
            p=FQ(0)
            for m in range(d+1):
                p += vec[z]*n**m;z+=1
            val += p*W[n+j]
        if val != target[n]:return False,n,val-target[n]
    return True,None,None


def verify_rational_exact(vec,W,target,r,dp,de):
    off=(r+1)*(dp+1)
    for n in range(len(target)-r):
        z=0; val=FQ(0)
        for j in range(r+1):
            p=FQ(0)
            for m in range(dp+1):p+=vec[z]*n**m;z+=1
            val+=p*W[n+j]
        E=sum(vec[off+m]*n**m for m in range(de+1))
        val-=E*target[n]
        if val:return False,n,val
    return True,None,None


def verify_rec_exact(vec,W,r,d):
    for n in range(len(W)-r):
        z=0;val=FQ(0)
        for j in range(r+1):
            p=FQ(0)
            for m in range(d+1):p+=vec[z]*n**m;z+=1
            val+=p*W[n+j]
        if val:return False,n,val
    return True,None,None

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    lines=[]
    lines.append('# Q4887 exact computation result')
    lines.append('')
    lines.append('Primes: '+', '.join(map(str,PRIMES)))
    all_mod={p:sequences_mod(p,NTERMS) for p in PRIMES}
    lines.append(f'Generated {NTERMS} exact/modular terms.')

    Wex=W_terms_exact(NTERMS)
    qex=q_terms_exact(NTERMS)
    hex=hA_terms_exact(NTERMS)
    qhex=[qex[n]/hex[n] for n in range(NTERMS)]

    # 1. Direct polynomial-only map.
    for key,target_exact in [('q',qex),('q_over_hA',qhex)]:
        cand=search_direct(all_mod,'q' if key=='q' else 'qh')
        lines.append('')
        lines.append(f'## Direct polynomial map to {key}')
        if not cand:
            lines.append(f'No identity target_n=sum_{{j=0}}^r P_j(n)W_(n+j) found for r<={MAX_R}, degree<={MAX_D_DIRECT}, with {HOLDOUT} or more holdout equations.')
        else:
            r,d,sols=cand[0]
            vec=reconstruct_vector(sols)
            lines.append(f'Candidate r={r}, degree={d}.')
            if vec is None:
                lines.append('CRT rational reconstruction failed.')
            else:
                ok,bad,res=verify_direct_exact(vec,Wex,target_exact,r,d)
                lines.append(f'Exact verification: {ok}; first bad={bad}.')
                for j in range(r+1):
                    lines.append(f'P_{j}(n) = {poly_to_str(vec[j*(d+1):(j+1)*(d+1)])}')

    # 2. Rational maps with common polynomial denominator.
    for key,target_exact in [('q',qex),('q_over_hA',qhex)]:
        cand=search_rational(all_mod,'q' if key=='q' else 'qh')
        lines.append('')
        lines.append(f'## Rational map to {key}')
        if not cand:
            lines.append(f'No E(n) target_n=sum P_j(n)W_(n+j) found in search bounds r<={MAX_R}, deg P/E<={MAX_D_RATIONAL}.')
        else:
            r,dp,de,norm,sols=cand[0]
            vec=reconstruct_vector(sols)
            lines.append(f'Candidate r={r}, degP={dp}, degE={de}, normalized coordinate={norm}.')
            if vec is None:
                lines.append('CRT rational reconstruction failed.')
            else:
                ok,bad,res=verify_rational_exact(vec,Wex,target_exact,r,dp,de)
                lines.append(f'Exact verification: {ok}; first bad={bad}.')
                for j in range(r+1):
                    lines.append(f'P_{j}(n) = {poly_to_str(vec[j*(dp+1):(j+1)*(dp+1)])}')
                off=(r+1)*(dp+1)
                lines.append(f'E(n) = {poly_to_str(vec[off:off+de+1])}')

    # 3. Minimal guessed annihilator of W.
    rec=search_recurrence(all_mod)
    lines.append('')
    lines.append('## Minimal recurrence search for W')
    if rec is None:
        lines.append(f'No recurrence found for order<={MAX_REC_ORDER}, degree<={MAX_REC_DEG}.')
    else:
        r,d,norm,sols=rec
        vec=reconstruct_vector(sols)
        lines.append(f'Candidate order={r}, degree={d}, normalized coordinate={norm}.')
        if vec is None:
            lines.append('CRT rational reconstruction failed.')
        else:
            ok,bad,res=verify_rec_exact(vec,Wex,r,d)
            lines.append(f'Exact verification: {ok}; first bad={bad}.')
            for j in range(r+1):
                lines.append(f'L_{j}(n) = {poly_to_str(vec[j*(d+1):(j+1)*(d+1)])}')

    Path('tmp/q4887_result.md').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))

if __name__=='__main__':
    main()
