# Generate the polynomial remainder Pq for the I17 Lean proof.
import sympy as sp
e, pi, z3, z5 = sp.symbols('e pi z3 z5')
R = sp.Rational
N = (4-6*e)*(3-6*e)*(2-6*e)*(1-6*e)
D = (2*e-1)*(3*e-1)*(3*e-2)*(2-3*e)*(1-3*e)*(3-4*e)*(2-4*e)*(1-4*e)
Xp = 2*pi**2 + 32*z3*e + R(44,15)*pi**4*e**2
e2L = (R(-1,6) + R(-35,36)*e + (-pi**2/3 - R(559,216))*e**2
       + (-R(16,3)*z3 - R(35,18)*pi**2 + R(2737,1296))*e**3)
P = sp.expand(N*(1+e**2*Xp) - 6*D*e2L)
poly = sp.Poly(P, e)
low = [poly.coeff_monomial(e**k) for k in range(4)]
print('low coeffs (must be 0):', [sp.simplify(c) for c in low])
Pq = sp.expand(P/e**4)
pp = sp.Poly(Pq, e)
terms=[]
for k in range(pp.degree()+1):
    c = sp.expand(pp.coeff_monomial(e**k))
    terms.append((k,c))
    print(k, c)
# check gamma exponent sums
cs = [(-1,3),(2,1),(3,1),(-6,1),(1,-3),(-3,-1),(-4,-1)]
for p in range(1,7): print(p, sum(m*a**p for a,m in cs))
