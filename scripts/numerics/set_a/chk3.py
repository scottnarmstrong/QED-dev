from numG import *
import pickle
sol=pickle.load(open('g3sol.pkl','rb'))
def ev(k,x):
    x=m.mpf(x)
    if k.startswith('P3['):
        a=k[3:-1]; f=m.mpf(sp.lambdify(U,sp.sympify(a),'mpmath')(x))
        return m.polylog(3,f)-m.log(abs(f))*m.polylog(2,f)
    return evalterm(k,x)
G=lambda x: sum(m.mpf(sp.Rational(v))*ev(k,x) for k,v in sol.items())
e=m.mpf('1e-30')
print(G(1-e)-G(e), 13*m.zeta(3)/18-7*m.pi**2*m.log(2)/9)
print('G3(0+)',G(e),'G3(1-)',G(1-e))
