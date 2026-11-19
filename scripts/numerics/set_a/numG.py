import mpmath as m, re, sympy as sp
m.mp.dps=40
U=sp.symbols('u')
def evalterm(k,x):
    x=m.mpf(x)
    env={'L0':m.log(x),'L1':m.log(1-x),'Lm':m.log(1+x),'l2':m.log(2),'z2':m.pi**2/6,'z3':m.zeta(3)}
    val=m.mpf(1)
    for fac in k.split('*l2*Li3['):
        pass
    def arg(s): return m.mpf(sp.lambdify(U,sp.sympify(s),'mpmath')(x))
    parts=re.findall(r'(P4|Li[234])\[([^\]]*)\]',k)
    rest=re.sub(r'(P4|Li[234])\[([^\]]*)\]','',k)
    for name,a in parts:
        f=arg(a)
        if name=='P4': val*=m.polylog(4,f)-m.log(abs(f))*m.polylog(3,f)
        else: val*=m.polylog(int(name[2]),f)
    for tok in rest.split('*'):
        if tok: val*=env[tok]
    return val
def G(sol,x): return sum(m.mpf(sp.Rational(v))*evalterm(k,x) for k,v in sol.items())
