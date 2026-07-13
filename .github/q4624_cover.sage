print('BEGIN_Q4624_COVER')
KU.<U> = FunctionField(QQ)
PV.<VV> = PolynomialRing(KU)
hU = U*(U^2+1)*(U^2+2*U-1)
L.<V> = KU.extension(VV^2-hU)

x = (1-U)/(1+U)
A0 = x^3+x^2-x+1
z = 4*V/(1+U)^3
y = (z-A0)/2
r = (x^2-x*y+y^2+y)/(x^2+x-y-1)
s = (x-y)/(x+1)
b = r*s*(r-1)
c = s*(r-1)
M = 16*b^2 - 8*b*c^2 - 20*b*c + b + c*(c-1)^3
D = b*M
coeff=D.list()
while len(coeff)<2: coeff.append(KU(0))
DA,DB=coeff[0],coeff[1]
S = U^3*(U-1)^8*(U^2-2*U-1)*(U^2+1)/((U+1)^7*(U^2+2*U-1)^3)
print('CHECK_NORM_MINUS_SQ=', D.norm()-S^2)
print('A_PLUS_S_FACTOR=',factor(2*(DA+S)))
print('A_MINUS_S_FACTOR=',factor(2*(DA-S)))
for lab,q in [('PLUS',2*(DA+S)),('MINUS',2*(DA-S))]:
 print(lab,'NUM_FACTOR=',factor(q.numerator()))
 print(lab,'DEN_FACTOR=',factor(q.denominator()))
 try:
  C=HyperellipticCurve(q.numerator()*q.denominator())
  print(lab,'GENUS=',C.genus())
  print(lab,'HYP_POLYS=',C.hyperelliptic_polynomials())
  print(lab,'SIMPLIFIED=',C.simplified_model())
 except Exception as e:
  print(lab,'ERR=',e)
print('END_Q4624_COVER')
