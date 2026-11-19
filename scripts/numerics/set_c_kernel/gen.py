"""Build the b-integrated hierarchical integrands G = E - e0 of the four two-loop units
with separate inner (mu) and outer (nu) photon masses, from the repository's exact
parametric engine (scripts/numerics/two_loop_unit_integrals.py). Output: units.pkl."""
import sys, pickle, time
sys.path.insert(0, '/home/scott/QED-dev/scripts/numerics')
import sympy as sp
import two_loop_unit_integrals as T
bS, MS, hS, betaS = T.bS, T.MS, T.hS, T.betaS
x = sp.Symbol('x', positive=True)
Y, y3, y4 = sp.symbols('Y y3 y4', positive=True)
b = sp.Symbol('b', positive=True)
out = {}
def build(name, Z, e, Din_expected):
    t0 = time.time()
    A, U, D0 = T.integrand_parts(name, Z)
    assert sp.simplify(D0 - Din_expected) == 0, name
    A2 = sp.factor(sp.together(A[2]*b/x**2)).subs(b, bS)
    A1 = sp.factor(sp.together(A[1]*b/x**2)).subs(b, bS)
    E, logc, e0 = T.b_integral(A2, A1, bS)
    out[name] = dict(E=E, logc=logc, e0=e0, A2=A2, A1=A1)
    print(name, 'logc =', logc, ' e0 =', sp.simplify(e0), f'({time.time()-t0:.0f}s)', flush=True)
c = Y*(1-Y)
w = b*(1-x)/x
build('L', [b - c, Y, w, 1-Y], 0, Y**2 + b**2/(b + w))
build('S+', [b - c, Y, w, 1-Y], 0, Y**2 + b**2/(b + w))
yb = 1 - y3 - y4
build('C+', [b - y3*yb, y3, y4, w - y3*y4, yb], y3*y4, (y3+y4)**2 + b**2/(b + w))
z2, z3 = y3, y4
build('X', [b - z2*yb, z2, z3, w - z2*z3, yb], z2*z3, (z2+z3)**2 + b**2/(b + w))
pickle.dump(dict(out=out), open('units.pkl', 'wb'))
