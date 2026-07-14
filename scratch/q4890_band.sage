from sage.all import *
from functools import reduce

print('Q4890 exact Jacobi/Christoffel-Darboux contiguous-band search')

# ============================================================
# 0. Rings
# ============================================================
Rn.<n> = PolynomialRing(QQ)
Kn = Rn.fraction_field()
RX.<X> = PolynomialRing(QQ)


def eval_rf(f, m):
    f = Kn(f)
    den = f.denominator()(m)
    if den == 0:
        raise ZeroDivisionError('denominator vanishes at n=%s: %s' % (m, f))
    return QQ(f.numerator()(m)) / QQ(den)


# ============================================================
# 1. Printed CMF and H-normalization
# ============================================================
def M_of(x):
    P = x.parent()
    m11 = (-2*x-5)*(x+3)**2*(136*x**4+1424*x**3+5548*x**2+9551*x+6141)
    m12 = 384*x**6+6384*x**5+44168*x**4+162698*x**3+336377*x**2+369933*x+169011
    m13 = -(480*x**4+4980*x**3+19210*x**2+32690*x+20730)

    m21 = (x+2)**2*(x+3)**2*(4*x+10)*(48*x**3+386*x**2+1017*x+879)
    m22 = -(x+2)**2*(272*x**5+3848*x**4+21732*x**3+61184*x**2+85761*x+47808)
    m23 = (x+2)**2*(320*x**3+2540*x**2+6610*x+5640)

    m31 = -(4*x+10)*(x+2)**2*(x+3)**2*(32*x**4+302*x**3+1037*x**2+1530*x+813)
    m32 = (x+2)**2*(192*x**6+2984*x**5+19116*x**4+64452*x**3+120256*x**2+117279*x+46476)
    m33 = -(x+2)**2*(16*x**5+408*x**4+2912*x**3+8884*x**2+12254*x+6240)
    return matrix(P, [[m11,m12,m13],[m21,m22,m23],[m31,m32,m33]])


def delta_H(x):
    return -2*(x+2)**2*(x+3)**2*(2*x+5)*(2*x+7)**2


def MH_of(x):
    return M_of(x) / delta_H(x)


# ============================================================
# 2. Scalar recurrence, selected output column 0
# ============================================================
def scalar_recurrence(column=0):
    e = vector(Kn, [1 if i == column else 0 for i in range(3)])
    vectors = [e]
    P = identity_matrix(Kn, 3)
    for j in range(1, 4):
        P = P * matrix(Kn, MH_of(n+j-1))
        vectors.append(P*e)

    coeffs = []
    for j in range(4):
        cols = [vectors[r] for r in range(4) if r != j]
        A = matrix(Kn, [list(v) for v in cols]).transpose()
        coeffs.append((-1)**j * A.det())

    common = Rn(1)
    for c in coeffs:
        common = lcm(common, Rn(Kn(c).denominator()))
    polys = [Rn(Kn(common)*c) for c in coeffs]
    g = reduce(gcd, [p for p in polys if p != 0])
    polys = [p//g for p in polys]

    coeff_values = [ZZ(abs(a)) for p in polys for a in p if a != 0]
    content = reduce(gcd, coeff_values) if coeff_values else ZZ(1)
    if content not in (0,1):
        polys = [p/content for p in polys]
    if polys[-1].leading_coefficient() < 0:
        polys = [-p for p in polys]
    return polys


ELL = scalar_recurrence(0)
print('normalized scalar recurrence degrees:', [p.degree() for p in ELL])
for j,p in enumerate(ELL):
    print('ell_%d factorization:' % j, factor(p))


# ============================================================
# 3. Exact normalized CMF pairs qhat*G - phat
# ============================================================
def cmf_pairs(Nmax, column=0):
    p = vector(QQ, [30921,-32972,8240])
    q = vector(QQ, [33750,-36000,9000])
    out = []
    for N in range(Nmax+1):
        out.append((q[column],p[column]))
        if N < Nmax:
            MH = matrix(QQ, MH_of(QQ(N)))
            p = p*MH
            q = q*MH
    return out


TARGET_MAX = 260
TARGET = cmf_pairs(TARGET_MAX,0)
print('target initial pairs:', TARGET[:3])


# ============================================================
# 4. Jacobi families
# ============================================================
def odd_harmonic(m):
    return sum(QQ(1,2*r+1) for r in range(m))


_J_CACHE = {}
def J_and_dJ(N):
    if N in _J_CACHE:
        return _J_CACHE[N]
    pref = rising_factorial(QQ(1,2),N)/factorial(N)
    J = RX(0)
    dJ = RX(0)
    for k in range(N+1):
        c = ((-1)**k * binomial(N,k) * pref
             * rising_factorial(QQ(N)+QQ(1,2),k)
             / rising_factorial(QQ(1,2),k))
        dlog = (2*odd_harmonic(N)
                + 2*sum(QQ(1,2*N+2*r+1) for r in range(k))
                - 2*odd_harmonic(k))
        J += c*X**k
        dJ += c*dlog*X**k
    _J_CACHE[N] = (J,dJ)
    return J,dJ


_R_CACHE = {}
def R_jacobi(N):
    if N in _R_CACHE:
        return _R_CACHE[N]
    J,dJ = J_and_dJ(N)
    B = J(-1)
    dB = dJ(-1)
    numerator = B*dJ-dB*J
    C,rem = numerator.quo_rem(X+1)
    assert rem == 0
    kappa = QQ(4*N+1,2)
    ans = RX(kappa*(B*J-(X+1)/2*(2*X*C.derivative()+C)))
    _R_CACHE[N] = ans
    return ans


_K_CACHE = {}
def K_jacobi(N):
    if N in _K_CACHE:
        return _K_CACHE[N]
    if N == 0:
        J,_ = J_and_dJ(0)
        ans = QQ(1,2)*J(-1)*J
    else:
        ans = K_jacobi(N-1)
        J,_ = J_and_dJ(N)
        ans += QQ(4*N+1,2)*J(-1)*J
    ans = RX(ans)
    _K_CACHE[N] = ans
    return ans


_P_CACHE = {}
def P_jacobi(N):
    if N in _P_CACHE:
        return _P_CACHE[N]
    J,_ = J_and_dJ(N)
    ans = RX(QQ(4*N+1,2)*J(-1)*J)
    _P_CACHE[N] = ans
    return ans


FAMILIES = {'R':R_jacobi,'K':K_jacobi,'P':P_jacobi}


# ============================================================
# 5. Exact Catalan moment pairs: integral = q*G-p
# ============================================================
def catalan_monomial_pair(k):
    q = QQ((-1)**k)
    partial = sum(QQ((-1)**j,(2*j+1)**2) for j in range(k))
    return q,q*partial


_PAIR_CACHE = {}
def moment_pair(P):
    q = QQ(0); p = QQ(0)
    for k,a in enumerate(P.list()):
        qk,pk = catalan_monomial_pair(k)
        q += a*qk; p += a*pk
    return q,p


def family_pair(name,N):
    key=(name,N)
    if key not in _PAIR_CACHE:
        _PAIR_CACHE[key]=moment_pair(FAMILIES[name](N))
    return _PAIR_CACHE[key]


# Basic diagnostics.
for name in ['R','K','P']:
    print(name,'initial moment pairs:',[family_pair(name,j) for j in range(3)])


def test_raw(name,Nmax=12):
    bad=[]
    for m in range(Nmax+1):
        for comp in (0,1):
            res=sum(QQ(ELL[j](m))*family_pair(name,m+j)[comp] for j in range(4))
            if res != 0:
                bad.append((m,comp,res)); break
        if bad: break
    print('raw family',name,'first residual:',bad[0] if bad else 'none')

for name in ['R','K','P']:
    test_raw(name)


# ============================================================
# 6. Linear band search with a common rational denominator D(n)
# ============================================================
PRIMES=[1000003,1000033,1000037]


def build_system(names,width,numdeg,D,Nrec,enforce_initial=True):
    D=Rn(D)
    labels=[(name,r,d) for name in names for r in range(width+1) for d in range(numdeg+1)]
    rows=[]; rhs=[]

    def weight(m,d):
        den=D(m)
        if den == 0:
            raise ZeroDivisionError('D(%d)=0 for %s' % (m,D))
        return QQ(m**d)/QQ(den)

    for m in range(Nrec+1):
        for comp in (0,1):
            row=[]
            for name,r,d in labels:
                val=QQ(0)
                for j in range(4):
                    val += QQ(ELL[j](m))*weight(m+j,d)*family_pair(name,m+j+r)[comp]
                row.append(val)
            rows.append(row); rhs.append(QQ(0))

    if enforce_initial:
        for m in range(3):
            for comp in (0,1):
                row=[weight(m,d)*family_pair(name,m+r)[comp] for name,r,d in labels]
                rows.append(row); rhs.append(TARGET[m][comp])
    return labels,matrix(QQ,rows),vector(QQ,rhs)


def modular_consistent(A,b):
    for p in PRIMES:
        F=GF(p)
        try:
            Ap=matrix(F,A.nrows(),A.ncols(),[F(x) for x in A.list()])
            bp=vector(F,[F(x) for x in b])
        except (ZeroDivisionError,ValueError):
            continue
        Aug=Ap.augment(matrix(F,len(bp),1,list(bp)))
        if Ap.rank()!=Aug.rank():
            return False,p,Ap.rank(),Aug.rank()
    return True,None,None,None


def verify_solution(sol,labels,D,Nverify=180):
    D=Rn(D)
    coeffs={}
    for name in sorted(set(x[0] for x in labels)):
        for r in sorted(set(x[1] for x in labels if x[0]==name)):
            num=Rn(0)
            for c,(nm,rr,d) in zip(sol,labels):
                if nm==name and rr==r and c:
                    num += QQ(c)*n**d
            if num:
                coeffs[(name,r)]=Kn(num/D)

    def candidate_pair(m):
        q=QQ(0); p=QQ(0)
        for (name,r),f in coeffs.items():
            w=eval_rf(f,m)
            qq,pp=family_pair(name,m+r)
            q += w*qq; p += w*pp
        return q,p

    for m in range(3):
        if candidate_pair(m)!=TARGET[m]:
            return False,coeffs,('initial',m,candidate_pair(m),TARGET[m])
    for m in range(Nverify+1):
        cp=candidate_pair(m)
        if cp!=TARGET[m]:
            return False,coeffs,('target',m,cp,TARGET[m])
    for m in range(Nverify-3):
        for comp in (0,1):
            res=sum(QQ(ELL[j](m))*candidate_pair(m+j)[comp] for j in range(4))
            if res:
                return False,coeffs,('recurrence',m,comp,res)
    return True,coeffs,None


def run_candidate(names,width,D,numdeg,margin=16):
    unknowns=len(names)*(width+1)*(numdeg+1)
    Nrec=max(14,(unknowns+margin)//2)
    if Nrec+width+4>TARGET_MAX:
        print('SKIP target cache too short')
        return None
    print('\nSEARCH names=%s width=%d Ddeg=%d numdeg=%d unknowns=%d Nrec=%d' %
          (names,width,Rn(D).degree(),numdeg,unknowns,Nrec))
    labels,A,b=build_system(names,width,numdeg,D,Nrec,True)
    ok,p,ra,rg=modular_consistent(A,b)
    if not ok:
        print('  modularly inconsistent mod',p,'rank',ra,'aug',rg)
        return None
    print('  survived modular screens; exact ranks...')
    Aug=A.augment(matrix(QQ,len(b),1,list(b)))
    ra=A.rank(); rg=Aug.rank()
    print('  exact rank',ra,'augmented',rg,'nullity',A.ncols()-ra)
    if ra!=rg:
        return None
    sol=A.solve_right(b)
    good,coeffs,why=verify_solution(sol,labels,D,min(180,TARGET_MAX-width-4))
    print('  exact verification:',good,why)
    if good:
        print('FOUND EXACT BAND')
        for key in sorted(coeffs):
            print('  %s_%d(n) = %s' % (key[0],key[1],factor(coeffs[key])))
        return coeffs
    return None


# ============================================================
# 7. Denominator supports
# ============================================================
def squarefree_product(polys,linear_only=False):
    seen=[]
    for p in polys:
        for f,e in factor(Rn(p)):
            f=Rn(f)
            lc=f.leading_coefficient()
            f=Rn(f/lc)
            if linear_only and f.degree()!=1:
                continue
            if f not in seen:
                seen.append(f)
    ans=Rn(1)
    for f in seen:
        # Omit factors with zeros at nonnegative search indices.
        if any(f(m)==0 for m in range(0,8)):
            continue
        ans*=f
    return Rn(ans)

D1=Rn(1)
Dmatrix=Rn((n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2)
Ddet=Rn((n+1)**5*(n+2)**3*(2*n+3)**2*(2*n+5)**2)
Dshift=Rn((n+1)*(n+2)*(n+3)*(n+4)*(2*n+1)*(2*n+3)*(2*n+5)*(2*n+7)*(2*n+9)*(2*n+11))
Dlin=squarefree_product(ELL,True)
Dend=squarefree_product([ELL[0],ELL[3]],False)
Dall=squarefree_product(ELL,False)

DENOMS=[('one',D1),('matrix',Dmatrix),('det',Ddet),('shift',Dshift),('linear',Dlin),('endpoints',Dend),('all',Dall)]
print('\nDENOMINATORS')
for nm,D in DENOMS:
    print(nm,'degree',D.degree(),'factor',factor(D))


# ============================================================
# 8. Search ladder
# ============================================================
FOUND=None

# Pure polynomial searches, exactly the claim in the question but broader degree.
for width in [2,3]:
    for deg in range(0,11):
        FOUND=run_candidate(('R','K'),width,D1,deg)
        if FOUND: break
    if FOUND: break

# Rational searches with singular-orbit denominator classes.
if FOUND is None:
    for width in [2,3]:
        for dname,D in DENOMS[1:]:
            growths=[-3,-2,-1,0,1,2]
            for growth in growths:
                numdeg=max(0,D.degree()+growth)
                unknowns=2*(width+1)*(numdeg+1)
                if unknowns>420:
                    print('SKIP',dname,'width',width,'numdeg',numdeg,'unknowns',unknowns)
                    continue
                FOUND=run_candidate(('R','K'),width,D,numdeg)
                if FOUND: break
            if FOUND: break
        if FOUND: break

# Optional enlargement by the non-derivative Jacobi product family.
if FOUND is None:
    print('\nNo R/K band found in the displayed ladder; testing R/K/P polynomial bands.')
    for width in [2,3]:
        for deg in range(0,7):
            FOUND=run_candidate(('R','K','P'),width,D1,deg)
            if FOUND: break
        if FOUND: break

print('\n============================================================')
if FOUND:
    print('FINAL RESULT: exact contiguous band found and verified through n=180.')
else:
    print('FINAL RESULT: NO solution in the full tested ladder.')
    print('This rules out widths 2 and 3 for R/K with polynomial coefficients of degree <=10,')
    print('and with the listed common denominator classes through numerator growth +2,')
    print('plus R/K/P polynomial bands through degree 6. It is not a universal no-go for arbitrary rational functions.')
print('============================================================')
