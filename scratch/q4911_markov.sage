from sage.all import *

# Q4911: Markov route for Problem 2.5.
# Exact QQ arithmetic except for decimal display.

N_SINGLE = 30
N_MOP = 30
PRINT_FULL_POLYS = False
napprox = numerical_approx

R.<x> = PolynomialRing(QQ)
K.<rt2> = QuadraticField(2)
rho = K(17) - K(12)*rt2
lam_plus = K(17) + K(12)*rt2


def m_sigma(k):
    # Integral_0^1 x^k (-log x)/(4 sqrt(x)) dx.
    return QQ(1, (2*k + 1)^2)


def m_base(k):
    # Integral_0^1 x^k dx/(2 sqrt(x)).
    return QQ(1, 2*k + 1)


def inner(p, q, moment):
    return sum(a*b*moment(i+j)
               for i, a in enumerate(p.list())
               for j, b in enumerate(q.list()))


def monic_op(deg, moment):
    if deg == 0:
        return R(1)
    H = matrix(QQ, deg, deg, lambda i, j: moment(i+j))
    rhs = vector(QQ, [-moment(deg+i) for i in range(deg)])
    c = H.solve_right(rhs)
    return R(x^deg + sum(c[j]*x^j for j in range(deg)))


print('Q4911 MARKOV / SIGMA-ORTHOGONAL COMPUTATION')
print('rho =', rho, 'approximately', napprox(rho, 45))
print('lambda_plus =', lam_plus, 'approximately', napprox(lam_plus, 45))
print()

# ------------------------------------------------------------------
# 1. Ordinary sigma-orthogonal polynomials.
# ------------------------------------------------------------------
Q = [monic_op(n, m_sigma) for n in range(N_SINGLE+1)]
for n, q in enumerate(Q):
    assert q[n] == 1
    assert all(inner(q, x^j, m_sigma) == 0 for j in range(n))

print('SINGLE-MEASURE MONIC OPS')
if PRINT_FULL_POLYS:
    for n, q in enumerate(Q):
        print('Q_%d(x) = %s' % (n, q))
else:
    for n in range(8):
        print('Q_%d(x) = %s' % (n, Q[n]))
    print('(Q_8 through Q_30 are constructed exactly; set PRINT_FULL_POLYS=True to print them.)')
print()

q_minus = [q(-1) for q in Q]
q_rho = [K(q(rho)) for q in Q]
print('EVALUATIONS')
print('n | Q_n(-1) exact | Q_n(rho), 55 digits')
for n in range(N_SINGLE+1):
    print('%2d | %s | %s' % (n, q_minus[n], napprox(q_rho[n], 55)))
print()

# Monic recurrence xQ_n=Q_{n+1}+a_n Q_n+b_n Q_{n-1}.
norms = [inner(q, q, m_sigma) for q in Q]
a = []
b = [None]
for n in range(N_SINGLE):
    an = inner(x*Q[n], Q[n], m_sigma)/norms[n]
    a.append(an)
    if n >= 1:
        b.append(norms[n]/norms[n-1])
    rem = x*Q[n] - Q[n+1] - an*Q[n]
    if n >= 1:
        rem -= b[n]*Q[n-1]
    assert rem == 0

print('LAST THREE-TERM RECURRENCE COEFFICIENTS')
print('n | a_n exact | b_n exact | decimals')
for n in range(max(1, N_SINGLE-8), N_SINGLE):
    print(n, a[n], b[n], napprox(a[n], 25), napprox(b[n], 25))
print('Regular-measure limits: a_n -> 1/2 and b_n -> 1/16.')
print()

limit_minus = -(K(3) + K(2)*rt2)/K(4)
print('RATIOS Q_{n+1}(-1)/Q_n(-1)')
print('Predicted monic ratio limit =', limit_minus, 'approximately', napprox(limit_minus, 55))
for n in range(N_SINGLE-10, N_SINGLE):
    rat = q_minus[n+1]/q_minus[n]
    print(n, napprox(rat, 55), 'error=', napprox(K(rat)-limit_minus, 35))
print()

# Markov numerator P_n(z)=Integral (Q_n(z)-Q_n(t))/(z-t) d sigma(t).
def markov_numerator(poly, z0=QQ(-1)):
    quo, rem = R(poly(z0)-poly).quo_rem(R(z0-x))
    assert rem == 0
    return sum(c*m_sigma(k) for k, c in enumerate(quo.list()))

P_minus = [markov_numerator(q) for q in Q]
Gnum = RealField(180)(catalan)
print('MARKOV APPROXIMANTS AT z=-1')
print('F(-1)=-G. n | P_n(-1)/Q_n(-1) | error versus -G')
for n in range(N_SINGLE+1):
    approx = RealField(180)(P_minus[n]/q_minus[n])
    if n <= 5 or n >= N_SINGLE-8:
        print(n, napprox(approx, 65), napprox(approx+Gnum, 50))
print()

# ------------------------------------------------------------------
# 2. CMF raw and H-normalized first-column denominator.
# ------------------------------------------------------------------
def M(n):
    m11 = (-2*n-5)*(n+3)^2*(136*n^4+1424*n^3+5548*n^2+9551*n+6141)
    m12 = 384*n^6+6384*n^5+44168*n^4+162698*n^3+336377*n^2+369933*n+169011
    m13 = -480*n^4-4980*n^3-19210*n^2-32690*n-20730
    m21 = (n+2)^2*(n+3)^2*(4*n+10)*(48*n^3+386*n^2+1017*n+879)
    m22 = (n+2)^2*(-272*n^5-3848*n^4-21732*n^3-61184*n^2-85761*n-47808)
    m23 = (n+2)^2*(320*n^3+2540*n^2+6610*n+5640)
    m31 = (-4*n-10)*(n+2)^2*(n+3)^2*(32*n^4+302*n^3+1037*n^2+1530*n+813)
    m32 = (n+2)^2*(192*n^6+2984*n^5+19116*n^4+64452*n^3+120256*n^2+117279*n+46476)
    m33 = (n+2)^2*(-16*n^5-408*n^4-2912*n^3-8884*n^2-12254*n-6240)
    return matrix(ZZ, [[m11,m12,m13],[m21,m22,m23],[m31,m32,m33]])


def delta_H(n):
    return -2*(n+2)^2*(n+3)^2*(2*n+5)*(2*n+7)^2

qraw_row = vector(ZZ, [33750,-36000,9000])
qhat_row = vector(QQ, [33750,-36000,9000])
qraw, qhat = [], []
for n in range(N_SINGLE+1):
    qraw.append(qraw_row[0])
    qhat.append(qhat_row[0])
    if n < N_SINGLE:
        Mn = M(n)
        qraw_row = qraw_row*Mn
        qhat_row = (qhat_row*matrix(QQ, Mn))/QQ(delta_H(n))

assert qhat[0] == 33750
assert qhat[1] == QQ(5295375,4)

print('CMF VALUES AND SINGLE-MEASURE COMPARISON')
print('n | Qhat_n | Qhat_{n+1}/Qhat_n | Qhat_n/Qsigma_n(-1)')
for n in range(N_SINGLE+1):
    step = None if n == N_SINGLE else qhat[n+1]/qhat[n]
    gauge = qhat[n]/q_minus[n]
    print(n, qhat[n], step, gauge, 'gauge decimal=', napprox(gauge, 35))
print()

print('CMF NORMALIZED RATIO LIMIT CHECK')
for n in range(N_SINGLE-10, N_SINGLE):
    rat = K(qhat[n+1]/qhat[n])
    print(n, napprox(rat, 55), 'error versus lambda_plus=', napprox(rat-lam_plus, 38))
print()

S.<nn> = PolynomialRing(QQ)

def rational_fit(values, pdeg, qdeg, train_count, verify_end):
    # Normalize q(0)=1; this covers rational functions finite at n=0.
    rows, rhs = [], []
    for n0 in range(train_count):
        v = QQ(values[n0])
        rows.append([QQ(n0)^j for j in range(pdeg+1)] +
                    [-v*QQ(n0)^j for j in range(1, qdeg+1)])
        rhs.append(v)
    A = matrix(QQ, rows)
    aug = A.augment(matrix(QQ, len(rhs), 1, rhs))
    if A.rank() != aug.rank():
        return None
    sol = A.solve_right(vector(QQ, rhs))
    p = sum(sol[j]*nn^j for j in range(pdeg+1))
    q = S(1) + sum(sol[pdeg+j]*nn^j for j in range(1, qdeg+1))
    for n0 in range(verify_end):
        if q(n0) == 0 or p(n0)/q(n0) != values[n0]:
            return None
    return p, q

r_single = [qhat[n]/q_minus[n] for n in range(N_SINGLE+1)]
print('LOW-DEGREE RATIONAL PATTERN SEARCH FOR Qhat_n/Qsigma_n(-1)')
found = []
for pd in range(7):
    for qd in range(7):
        need = pd+qd+1
        if need+6 <= len(r_single):
            ans = rational_fit(r_single, pd, qd, need+2, len(r_single))
            if ans is not None:
                found.append((pd, qd, ans))
print('found =', found)
print()

# ------------------------------------------------------------------
# 3. Natural type-II two-weight system.
# dmu0=dx/(2sqrt x), dmu1=(-log x)dx/(4sqrt x).
# This is a confluent Jacobi/AT system, not a genuine Nikishin pair.
# ------------------------------------------------------------------
def multiple_op(n0, n1):
    deg = n0+n1
    if deg == 0:
        return R(1)
    rows, rhs = [], []
    for j in range(n0):
        rows.append([m_base(j+k) for k in range(deg)])
        rhs.append(-m_base(j+deg))
    for j in range(n1):
        rows.append([m_sigma(j+k) for k in range(deg)])
        rhs.append(-m_sigma(j+deg))
    A = matrix(QQ, rows)
    assert A.nrows() == deg and A.det() != 0
    c = A.solve_right(vector(QQ, rhs))
    return R(x^deg + sum(c[k]*x^k for k in range(deg)))

T, indices = [], []
for deg in range(N_MOP+1):
    idx = (deg//2, deg//2) if deg % 2 == 0 else ((deg+1)//2, (deg-1)//2)
    indices.append(idx)
    T.append(multiple_op(*idx))

print('TYPE-II CONFLUENT TWO-WEIGHT STEP-LINE SYSTEM')
print('weights: dmu0=dx/(2sqrt x), dmu1=(-log x)dx/(4sqrt x)')
print('This is an AT/confluent Jacobi system on one interval, not a genuine Nikishin system.')
for deg in range(8):
    print(deg, indices[deg], T[deg])
print()

print('FOUR-TERM RECURRENCE SUPPORT')
rec = []
for deg in range(N_MOP):
    rem = R(x*T[deg]-T[deg+1])
    coeff = {}
    for j in range(deg, -1, -1):
        cj = rem[j]
        if cj:
            coeff[j] = cj
            rem -= cj*T[j]
    assert rem == 0
    assert not [j for j in coeff if j < deg-2], (deg, coeff)
    rec.append(coeff)
    if deg >= 2 and (deg <= 8 or deg >= N_MOP-6):
        print('degree=', deg,
              'b=', coeff.get(deg,0),
              'c=', coeff.get(deg-1,0),
              'd=', coeff.get(deg-2,0))
print('All lower coefficients vanish exactly: this is a four-term step-line recurrence.')
print()

Tminus = [p(-1) for p in T]
macro_max = N_MOP//2
macro_gauge = []
print('TWO-WEIGHT VALUES AT -1 AND MACRO-STEP TEST')
print('n | T_{2n}(-1) | 16*T_{2n+2}/T_{2n} | Qhat_n/(16^n*T_{2n})')
for n in range(macro_max+1):
    gauge = qhat[n]/(QQ(16)^n*Tminus[2*n])
    macro_gauge.append(gauge)
    macro_ratio = None if n == macro_max else QQ(16)*Tminus[2*n+2]/Tminus[2*n]
    print(n, Tminus[2*n], macro_ratio, gauge, napprox(gauge, 40))
print('16*((3+2sqrt2)/4)^2 = 17+12sqrt2, so the macro dominant scale agrees asymptotically.')
print()

print('LOW-DEGREE RATIONAL PATTERN SEARCH FOR Qhat_n/(16^n*T_{2n}(-1))')
found_macro = []
for pd in range(6):
    for qd in range(6):
        need = pd+qd+1
        if need+3 <= len(macro_gauge):
            ans = rational_fit(macro_gauge, pd, qd, need+1, len(macro_gauge))
            if ans is not None:
                found_macro.append((pd, qd, ans))
print('found_macro =', found_macro)
print()

print('LAST TWO-WEIGHT FOUR-TERM COEFFICIENTS, DECIMAL')
for deg in range(max(2, N_MOP-8), N_MOP):
    coeff = rec[deg]
    print(deg,
          napprox(coeff.get(deg,0), 35),
          napprox(coeff.get(deg-1,0), 35),
          napprox(coeff.get(deg-2,0), 35))
print()

print('FINAL FINDINGS')
print('1. Ordinary sigma-OPs have a three-term recurrence and their ratio at -1 tends to -(3+2sqrt2)/4, not 17+12sqrt2.')
print('2. CMF/ordinary-OP ratios are rational termwise, but no rational function of n of bidegree <=(6,6) fits n=0..30.')
print('3. The natural rational-moment two-weight system has an exact four-term recurrence.')
print('4. Its even contraction, multiplied by 16^n, has the CMF dominant scale, but no scalar rational gauge of bidegree <=(5,5) fits the finite data.')
print('5. The natural pair is confluent/AT, not Nikishin. A genuine Nikishin realization needs extra disjoint-support data and is not determined by the scalar CMF recurrence alone.')
