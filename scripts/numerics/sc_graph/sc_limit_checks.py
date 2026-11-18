"""Exact checks behind QED/TwoLoop/UnitSCLimit*.lean (S + C link, stages 1-4 for S).

Run: nice -n 10 python3 scripts/numerics/sc_graph/sc_limit_checks.py   (sympy, mpmath; < 1 min)
Prints only; writes no files. Each section is an independent check:
  1. S: b-integration by the five ladder masters (selfAX_eq, selfGm), symbolic + quadrature;
  2. C: masters 6, 7 and the b-decomposition of eq. (6.2) (cornerAX_eq, cForm);
  3. S: the coefficient of log M_Lambda is (1-Y)/2 vk + vm pointwise (selfEll_eq);
  4. S: sForm = -l A + (k1/h) phi1(u) + (k2/h^2) phi2(u) (sForm_eq_phi);
  5. S: G_S at lambda = 0 and its x-antiderivative, integral = K_S (selfR0, selfR0Anti);
  6. S: the coefficients of G_S at lambda = 0 (selfR_zero_eq).
"""
# ---- section: s_masters.py
def _sec_s_masters():
    import sympy as sp, mpmath as mp
    Y,x,b,M,h,c=sp.symbols('Y x b M h c',positive=True)
    k2=x**2*(x-1)*(Y*x-Y-x+3)/4
    k1=-x*(x-1)*(2*Y*x+Y-2*x+2)/2
    D=M+b*h
    A2=k2*(b-c)**2/b; A1=k1*(b-c)**2/b**2
    f=A2/D**2+A1/D
    K=k1+k2/h
    form=K/D+(-k2*M/h-2*c*k2)/D**2+k2*c**2/(b*D**2)-2*c*k1/(b*D)+k1*c**2/(b**2*D)
    print(sp.simplify(f-form))
    # masters values
    L=sp.log(1+M/(c*h))
    G=(-K*sp.log(M+c*h)/h+(-k2*M/h-2*c*k2)/(h*(M+c*h))+k2*c**2*(L/M**2-1/(M*(M+c*h)))
       -2*c*k1*L/M+k1*c**2*(1/(M*c)-h*L/M**2))
    # numeric check of difference at two M values vs quadrature
    mp.mp.dps=30
    vals={Y:mp.mpf('0.3'),x:mp.mpf('0.6'),h:mp.mpf('0.9')}
    cc=vals[Y]*(1-vals[Y])
    fn=sp.lambdify((b,M,c,Y,x,h),f,'mpmath'); Gn=sp.lambdify((M,c,Y,x,h),G,'mpmath')
    M1,M2=mp.mpf('0.2'),mp.mpf('5')
    q=mp.quad(lambda bb: fn(bb,M1,cc,vals[Y],vals[x],vals[h])-fn(bb,M2,cc,vals[Y],vals[x],vals[h]),[cc,1,10,mp.inf])
    print(q, Gn(M1,cc,vals[Y],vals[x],vals[h])-Gn(M2,cc,vals[Y],vals[x],vals[h]))

_sec_s_masters()

# ---- section: c_masters.py
def _sec_c_masters():
    import sympy as sp, mpmath as mp
    b,M,h,B=sp.symbols('b M h beta',positive=True)
    D=M+b*h
    L=sp.log(1+M/(B*h))
    m6=1/(M**2*B)-2*h*L/M**3+h/(M**2*(M+B*h))
    m7=1/(2*M*B**2)-h/(M**2*B)+h**2*L/M**3
    # check derivatives of antiderivatives: Phi6 with Phi6(inf)=0? use numeric quad
    mp.mp.dps=30
    for (Mv,hv,Bv) in [(0.3,0.7,0.2),(2.0,0.1,1.5)]:
        f6=lambda bb: 1/(bb**2*(Mv+bb*hv)**2); f7=lambda bb: 1/(bb**3*(Mv+bb*hv))
        print(mp.quad(f6,[Bv,mp.inf]), sp.N(m6.subs({M:Mv,h:hv,B:Bv}),20))
        print(mp.quad(f7,[Bv,mp.inf]), sp.N(m7.subs({M:Mv,h:hv,B:Bv}),20))
    # decomposition of C integrand
    x,y3,y4,g,e=sp.symbols('x y3 y4 g e')
    p1=(2*x**3*y3**2 - 2*x**3*y3 - 6*x**2*y3**2 - 4*x**2*y3*y4 + 6*x**2*y3 + 2*x**2*y4 - x**2
              + 6*x*y3**2 + 8*x*y3*y4 - 6*x*y3 + 2*x*y4**2 - 6*x*y4 - 2*y3**2 - 4*y3*y4 + 4*y3
              - 2*y4**2 + 4*y4)
    p2=(8*x**2*y3**2 - 8*x**2*y3 - 10*x*y3**2 - 4*x*y3*y4 + 2*x*y3 - 2*x*y4 + 5*x + 2*y3**2
              + 4*y3 - 2*y4**2 + 4*y4 - 4)
    q=x*(2-x)*(1-2*y3); r=3*x*(1-2*y3)
    A2=x*(b-g)*(p1*b+q*g)/(4*b**2); A1=-x*(b-g)*(2*(x-1)*b**2+p2*b-r*g)/(4*b**3)
    a0=x/4*p1; a1=x/4*g*(q-p1); a2=-x/4*q*g**2
    c0=-x/4*2*(x-1); c1=-x/4*(p2-2*(x-1)*g); c2=-x/4*(-r*g-p2*g); c3=-x/4*r*g**2
    form=a0/D**2+a1/(b*D**2)+a2/(b**2*D**2)+c0/D+c1/(b*D)+c2/(b**2*D)+c3/(b**3*D)
    print('decomp', sp.simplify(A2/D**2+A1/D-form))

_sec_c_masters()

# ---- section: ell.py
def _sec_ell():
    import sympy as sp
    Y,x,l=sp.symbols('Y x lam',positive=True)
    mx=x**2+(1-x)*l**2; h=mx/x
    k2=x**2*(x-1)*(Y*x-Y-x+3)/4
    k1=-x*(x-1)*(2*Y*x+Y-2*x+2)/2
    ell=k1/h+k2/h**2
    vk=x**2*(x-1)*(3*x**3+3*x**2+l**2*(2+2*x-4*x**2))/(2*mx**2)
    vm=x**2*(1-x)*(2*x**2+3*l**2*(1-x))/(2*mx**2)
    d=sp.simplify(ell-((1-Y)/2*vk+vm))
    print('diff',sp.factor(d))
    # antiderivative?
    F=sp.integrate(sp.together(d),x)
    print(sp.simplify(F))

_sec_ell()

# ---- section: phi.py
def _sec_phi():
    import sympy as sp
    k1,k2,c,h,M,A=sp.symbols('k1 k2 c h M A',positive=True)
    u=M/(c*h); B=sp.Symbol('B')
    sF=(-(k1+k2/h)*A/h+(-(k2*M/h)-2*c*k2)*(1/(h*(M+c*h)))+k2*c**2*(B/M**2-1/(M*(M+c*h)))
       -2*c*k1*(B/M)+k1*c**2*(1/(M*c)-h*B/M**2))
    phi1=1/u-2*B/u-B/u**2
    phi2=-1+(B-u)/u**2
    alt=-(k1/h+k2/h**2)*A+(k1/h)*phi1+(k2/h**2)*phi2
    print(sp.simplify(sF-alt))

_sec_phi()

# ---- section: sAnti.py
def _sec_sAnti():
    import sympy as sp
    Y,x=sp.symbols('Y x',positive=True)
    W=Y+(1-Y)*x
    cW=sp.expand(-(x-1)*W*(5*Y**2*x**2 - 2*Y**2*x - 3*Y**2 - 10*Y*x**2 + 9*Y*x - Y + 5*x**2 - 7*x)/(4*Y**2))
    cx=sp.expand(-x*(Y-1)*(x-1)*(5*Y**2*x**2 - 7*Y**2*x - 4*Y**2 - 10*Y*x**2 + 14*Y*x - 8*Y + 5*x**2 - 7*x)/(4*Y**2))
    cY=sp.expand((x-1)*(3*Y*x+3*Y-3*x+1)/4)
    rat=sp.expand(x*(Y-1)*(x-1)*(5*Y*x+Y-5*x+7)/(4*Y))
    a,b=sp.symbols('a b')  # log Y, log(1-Y)
    A=sp.integrate(cx,x)            # A(0)=0
    x0=-Y/(1-Y)
    B=sp.integrate(cW,x); B=sp.expand(B-B.subs(x,x0))
    Ax=sp.cancel(A/x); Q=sp.cancel(B*(1-Y)/W)
    print('Ax poly?',sp.Poly(Ax,x).degree(), ' Q poly?', sp.fraction(sp.together(Q))[1].free_symbols)
    C=sp.integrate(sp.expand(rat+cx*b+cY*a-Ax-Q),x)
    C=sp.expand(C-C.subs(x,0))
    Lx,LW=sp.symbols('Lx LW')
    F=A*Lx+B*LW+C
    # check derivative
    R0=rat+cW*LW+cx*(Lx+b)+cY*a
    dF=sp.diff(A,x)*Lx+A/x+sp.diff(B,x)*LW+B*(1-Y)/W+sp.diff(C,x)
    print('deriv check', sp.simplify(dF-R0))
    val=sp.simplify((F.subs({x:1,Lx:0,LW:0}))-(F.subs({x:0,Lx:0,LW:a})))
    KS=(1-Y)*(3*Y**2+2*Y+1)*b/(12*Y**2)+(3*Y**2-3*Y+2)/(24*Y)+Y*(9*Y-8)*a/(12*(1-Y))
    print('value check', sp.simplify(val-KS))
    def coeffs(p):
        P=sp.Poly(p,x); return [sp.factor(P.coeff_monomial(x**k)) for k in range(P.degree()+1)]
    print('A',coeffs(A)); print('B',coeffs(B)); print('C',coeffs(C)); print('Q',coeffs(Q))
    print('B(0)', sp.factor(B.subs(x,0)))

_sec_sAnti()

# ---- section: sR0.py (the coefficients of G_S(0) used in section sAnti)
def _sec_sR0():
    import sympy as sp
    Y,x=sp.symbols('Y x',positive=True)
    LW,Lx,LY,L1=sp.symbols('LW Lx LY L1')
    k2=x**2*(x-1)*(Y*x-Y-x+3)/4
    k1=-x*(x-1)*(2*Y*x+Y-2*x+2)/2
    c=Y*(1-Y); h=x; M=Y**2
    A=LY+LW            # log(M+ch) = log Y + log W
    B=LW-L1-Lx         # log(1+M/(ch))
    G=(-(k1+k2/h)*A/h+(-(k2*M/h)-2*c*k2)*(1/(h*(M+c*h)))+k2*c**2*(B/M**2-1/(M*(M+c*h)))
       -2*c*k1*(B/M)+k1*c**2*(1/(M*c)-h*B/M**2))
    W=Y+(1-Y)*x
    R0=sp.expand(G+k2/h**2)
    R0=R0.subs(M+c*h, Y*W)
    coef={}
    for s in (LW,Lx,LY,L1):
        coef[s]=sp.factor(sp.simplify(sp.diff(R0,s)))
    rat=sp.factor(sp.simplify(R0.subs({LW:0,Lx:0,LY:0,L1:0})))
    for s in coef: print(s, coef[s])
    print('rat', rat)

_sec_sR0()
