#!/usr/bin/env python3
"""The exact evaluation of the corner unit C at lambda = 0 (sections 6.6.1-6.6.2 of
docs/TWO-LOOP-UNITS.md). NOT a proof by itself: generates the rational data of
QED/TwoLoop/UnitSCCorner{XDefs,XRat,XEnds}.lean (x-integration) and, through
corner_xi_integration.py, of QED/TwoLoop/UnitSCCornerXi{Defs,Rat,Ends}.lean (xi-integration), and
checks every identity used there in exact rational arithmetic (sympy).

Stages (each prints its checks):
  engine_phi       Phi_C = int_0^1 G_C dx from the engine of two_loop_unit_integrals.py;
  lean_letters     G_C = cornerGm 0 0 (Lean definitions of UnitSCLimitCMasters.lean, transcribed)
                   = R + (K - c0/h) log(M + beta h) - K log(beta h), on both branches of beta;
  antiderivatives  polynomial antiderivatives in x on [0, x*] and [x*, 1]; F' = G_C exactly;
  phi_coefficients the coefficients of Phi_C in the letters (engine);
  endpoints        F1(x*) - F1(0) + F2(1) - F2(x*) has exactly the coefficients of Phi_C;
  lean_defs, split_branch2, terms_branch2   emit Lean blocks (*.lean.block);
  xi_letters       Y Phi_C in the letters, and its xi-antiderivative (xi_integration.py);
then corner_xi_integration.py checks F(1-) - F(0+) = cornerKernel (UnitC.lean) exactly and emits
the xi blocks.

Run (single process, a few minutes, < 1 GB):
    nice -n 10 python3 scripts/numerics/sc_graph/corner_integration.py OUTDIR
Writes only to OUTDIR (pickles and *.lean.block files). The blocks occur verbatim (up to line
wrapping) in the Lean files, except that the xi blocks keep the names of xi_integration.py: the
Lean files prefix them with `c` (xiR0 -> cxiR0) and give the hypotheses of the *_eq lemmas the
default `:= by assumption`.
"""
import os
import runpy
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NUM = os.path.normpath(os.path.join(HERE, '..'))
CROSSED = os.path.join(NUM, 'crossed_graph')

STAGES = {}

def stage_engine_phi():
    """Phi_C from the engine of two_loop_unit_integrals.py (section 6.6.1), for comparison."""
    import sys, pickle
    sys.path.insert(0, NUM)
    import two_loop_unit_integrals as T
    import sympy as sp, mpmath as mp
    xi, co, (d1,d2), (y3,y4,x,G) = T.corner_x_integral()
    pickle.dump((xi,co,d1,d2,y3,y4,x,G), open('docphi.pkl','wb'))
    Phi=T._cc_phi_expr(xi,co)
    f=sp.lambdify((T._CX_Y,xi),Phi,'mpmath')
    mp.mp.dps=25
    for Y_,s in [(0.3,0.2),(0.8,0.65),(0.01,0.3)]:
        print(Y_,s,f(mp.mpf(Y_),mp.mpf(s)))


STAGES['engine_phi'] = stage_engine_phi

def stage_lean_letters():
    """the letter coefficients of G_C = cornerGm 0 0 on the two branches, from the Lean definitions."""
    import sympy as sp, pickle
    Y,xi,x=sp.symbols('Y xi x',positive=True)
    y3=Y*xi; y4=Y*(1-xi)
    p1=(2*x**3*y3**2 - 2*x**3*y3 - 6*x**2*y3**2 - 4*x**2*y3*y4 + 6*x**2*y3 + 2*x**2*y4 - x**2
        + 6*x*y3**2 + 8*x*y3*y4 - 6*x*y3 + 2*x*y4**2 - 6*x*y4 - 2*y3**2 - 4*y3*y4 + 4*y3 - 2*y4**2 + 4*y4)
    p2=(8*x**2*y3**2 - 8*x**2*y3 - 10*x*y3**2 - 4*x*y3*y4 + 2*x*y3 - 2*x*y4 + 5*x + 2*y3**2
        + 4*y3 - 2*y4**2 + 4*y4 - 4)
    g=y3*(1-y3-y4); q=x*(2-x)*(1-2*y3); r=3*x*(1-2*y3)
    a0=x/4*p1; a1=x/4*g*(q-p1); a2=-(x/4*q*g**2); c0=x*(1-x)/2
    c1=-(x/4*(p2-2*(x-1)*g)); c2=x/4*g*(r+p2); c3=-(x/4*r*g**2)
    M=Y**2; h=x
    KL=sp.cancel(a1/M**2-2*a2*h/M**3+c1/M-c2*h/M**2+c3*h**2/M**3)
    CW=sp.cancel(KL-c0/h); CB=sp.cancel(-KL)
    def R(be): return sp.cancel(a0/(h*(M+be*h))-a1/(M*(M+be*h))+a2*(1/(M**2*be)+h/(M**2*(M+be*h)))+c2/(M*be)+c3*(1/(2*M*be**2)-h/(M**2*be)))
    R1=R(g)
    e=Y**2*xi*(1-xi)
    R2=R(e*x/(1-x))
    print('CW',sp.factor(CW)); print('CB',sp.factor(CB)); print('CW+CB',sp.factor(CW+CB))
    print('R1',sp.factor(R1)); print('R2',sp.factor(R2))
    pickle.dump((CW,CB,R1,R2),open('xgen.pkl','wb'))


STAGES['lean_letters'] = stage_lean_letters

def stage_antiderivatives():
    """the x-antiderivatives on [0, x*] and [x*, 1]; derivative identities exact."""
    import sympy as sp, pickle
    Y,xi,x=sp.symbols('Y xi x',positive=True)
    CW,CB,R1,R2=pickle.load(open('xgen.pkl','rb'))
    DOM=sp.QQ.frac_field(Y,xi)
    P=lambda e: sp.Poly(sp.cancel(e),x,domain=DOM)
    def integ0(e):  # antiderivative vanishing at 0
        return P(e).integrate()
    xs=(1-Y)/(1-Y*xi)
    # branch 1
    B1=integ0((x-1)/2)
    Q1=integ0(CB)
    Q1x=sp.Poly(sp.cancel(Q1.as_expr()/x),x,domain=DOM)
    root=-Y/(xi*(1-Y))
    Ct=integ0(CW); C1=Ct-P(Ct.as_expr().subs(x,root))
    W=Y+xi*(1-Y)*x
    Tq,rem=sp.div(C1*P(xi*(1-Y)),P(W)); assert rem.is_zero
    T=Tq.integrate()
    P1=integ0(R1)
    A1=P1-Q1x.integrate()-T   # F1 = A1 + B1 logY + Q1(lxi+l1Y) + Q1x (x log x) + C1 log W
    # check derivative
    lY,lxi,l1Y,lx,lW=sp.symbols('lY lxi l1Y lx lW')
    F1d=(sp.diff(A1.as_expr(),x)+sp.diff(B1.as_expr(),x)*lY+sp.diff(Q1.as_expr(),x)*(lxi+l1Y)
         +sp.diff(Q1x.as_expr(),x)*x*lx+Q1x.as_expr()*(lx+1)+sp.diff(C1.as_expr(),x)*lW+C1.as_expr()*xi*(1-Y)/W)
    G1=R1+(x-1)/2*lY+CB*(lxi+l1Y+lx)+CW*lW
    def zero(E, syms):
        E=sp.expand(E)
        Pp=sp.Poly(E,*syms)
        return all(sp.cancel(c)==0 for c in Pp.coeffs())
    def zero(E, syms):
        Pp = sp.Poly(sp.expand(E), *syms)
        return all(sp.cancel(c) == 0 for c in Pp.coeffs())
    print('branch1 deriv ok', zero(F1d - G1, [lY, lxi, l1Y, lx, lW]), flush=True)
    # branch 2: R2 = poly + Aa/(1-xi x) + Bb/(1-(1-xi)x)
    n,d=sp.fraction(sp.factor(R2))
    Aa=sp.cancel(sp.cancel(R2*(1-xi*x)).subs(x,1/xi)); Bb=sp.cancel(sp.cancel(R2*(1-(1-xi)*x)).subs(x,1/(1-xi)))
    poly=sp.cancel(R2-Aa/(1-xi*x)-Bb/(1-(1-xi)*x))
    assert not sp.fraction(poly)[1].has(x)
    print('Aa',sp.factor(Aa)); print('Bb',sp.factor(Bb))
    Ca=Ct-P(Ct.as_expr().subs(x,1/xi)); Cb=Ct-P(Ct.as_expr().subs(x,1/(1-xi)))
    Ta,ra=sp.div(Ca*P(xi),P(1-xi*x)); assert ra.is_zero   # int Ca*(-xi)/(1-xi x) = -int Ta
    Tb,rb=sp.div(Cb*P(1-xi),P(1-(1-xi)*x)); assert rb.is_zero
    C2a=Ca-P(Aa/xi); C2b=Cb-P(Bb/(1-xi))
    Ut=P(-(1-x)**2/4)
    A2=integ0(poly)+P((1-x)/4).integrate()*(-1)*0  # placeholder
    # rational: A2' + Ut*(-1/(1-x)) + 2Q1/x + Ca*(-xi)/(1-xi x) + Cb*(-(1-xi))/(..) = R2 ; Ut*(-1/(1-x)) = (1-x)/4
    # with Ca(-xi)/(1-xi x) = -Ta ; Cb... = -Tb ; constants -Aa/xi * (-xi)/(1-xi x) = Aa/(1-xi x)
    A2=integ0(poly) - P((1-x)/4).integrate() - 2*Q1x.integrate() + Ta.integrate() + Tb.integrate()
    B2=2*B1
    Utx=P(-(1-x)/4)
    l1x,lA,lB,l1xi=sp.symbols('l1x lA lB l1xi')
    F2=lambda xx: None
    F2d=(sp.diff(A2.as_expr(),x)+sp.diff(B2.as_expr(),x)*lY+sp.diff(Utx.as_expr(),x)*(1-x)*l1x+Utx.as_expr()*(-l1x-1)
         +sp.diff(Q1.as_expr(),x)*(lxi+l1xi)+2*sp.diff(Q1.as_expr(),x)*lx+2*Q1.as_expr()/x
         +sp.diff(C2a.as_expr(),x)*lA+C2a.as_expr()*(-xi)/(1-xi*x)+sp.diff(C2b.as_expr(),x)*lB+C2b.as_expr()*(-(1-xi))/(1-(1-xi)*x))
    G2=R2+(x-1)*lY+(1-x)/2*l1x+CB*(lxi+l1xi+2*lx)+CW*(lA+lB)
    rat2=sp.diff(A2.as_expr(),x)+(1-x)/4+2*Q1x.as_expr()+C2a.as_expr()*(-xi)/(1-xi*x)+C2b.as_expr()*(-(1-xi))/(1-(1-xi)*x)-R2
    print('branch2 rat ok', sp.cancel(sp.together(rat2))==0, flush=True)
    print('branch2 C ok', sp.cancel(sp.diff(C2a.as_expr(),x)-CW)==0, sp.cancel(sp.diff(C2b.as_expr(),x)-CW)==0, flush=True)
    pieces=dict(B1=B1,Q1=Q1,Q1x=Q1x,C1=C1,A1=A1,A2=A2,B2=B2,Utx=Utx,C2a=C2a,C2b=C2b)
    for k,v in pieces.items():
        print(k,'deg',v.degree(), 'len',len(str(v.as_expr())), [sp.factor(sp.fraction(sp.factor(c))[1]) for c in v.all_coeffs()])
    pickle.dump((pieces,Aa,Bb,poly),open('xanti.pkl','wb'))


STAGES['antiderivatives'] = stage_antiderivatives

def stage_phi_coefficients():
    """the coefficients of Phi_C from the engine, in the letters."""
    import pickle, sympy as sp
    xi_,cod,*_=pickle.load(open('docphi.pkl','rb'))
    Y,xi=sp.symbols('Y xi',positive=True)
    co={}
    m={'1':'1','LY':'Y','Lxi':'xi','LA':'1-Y*xi','LB':'xi+Y-2*Y*xi'}
    for k,v in m.items():
        e=sp.sympify(cod[v]); e=e.subs({s:(Y if s.name=='Y' else xi) for s in e.free_symbols})
        co[k]=sp.factor(e)
    pickle.dump(co,open('phico.pkl','wb'))
    print({k:sp.fraction(v)[1] for k,v in co.items()})


STAGES['phi_coefficients'] = stage_phi_coefficients

def stage_endpoints():
    """F1(x*) - F1(0) + F2(1) - F2(x*) = Phi_C, coefficient by coefficient (exact); emits xends.lean.block."""
    import sys, pickle
    sys.path.insert(0, CROSSED)
    import xi_integration as XI
    import sympy as sp
    Y,xi,x=sp.symbols('Y xi x',positive=True)
    pieces,Aa,Bb,poly=pickle.load(open('xanti.pkl','rb'))
    co=pickle.load(open('phico.pkl','rb'))
    xs=sp.Symbol('xs')
    at=dict(A1s=('A1',xs),Q1s=('Q1x',xs),C1s=('C1',xs),A10=('A1',0),C10=('C1',0),
            A21=('A2',1),Q11=('Q1x',1),C2a1=('C2a',1),C2b1=('C2b',1),A2s=('A2',xs),C2as=('C2a',xs),C2bs=('C2b',xs))
    S={k:sp.Symbol(k) for k in at}
    LY,Lxi,L1Y,L1xi,LA,LB=sp.symbols('LY Lxi L1Y L1xi LA LB')
    lxs=L1Y-LA; lW=LB-LA; l1xs=LY+L1xi-LA; lAs=L1xi-LA; lBs=LB-LA
    F1xs=S['A1s']+(xs**2/4-xs/2)*LY+xs*S['Q1s']*(Lxi+L1Y)+S['Q1s']*(xs*lxs)+S['C1s']*lW
    F10=S['A10']+S['C10']*LY
    F21=S['A21']+(sp.Rational(1,2)-1)*LY+1*S['Q11']*(Lxi+L1xi)+S['C2a1']*L1xi+S['C2b1']*Lxi
    F2xs=(S['A2s']+(xs**2/2-xs)*LY-(1-xs)/4*((1-xs)*l1xs)+xs*S['Q1s']*(Lxi+L1xi)+2*(xs*S['Q1s'])*lxs
          +S['C2as']*lAs+S['C2bs']*lBs)
    Phi=sp.expand(F1xs-F10+(F21-F2xs))
    logs=[('LY','log Y','cφY'),('Lxi','log ξ','cφx'),('L1Y','log (1 - Y)',None),('L1xi','log (1 - ξ)',None),
          ('LA','log (1 - Y * ξ)','cφA'),('LB','log (ξ + Y - 2 * Y * ξ)','cφB')]
    coefs={k:sp.expand(sp.diff(Phi,sp.Symbol(k))) for k,_,_ in logs}
    coefs['1']=sp.expand(Phi.subs({sp.Symbol(k):0 for k,_,_ in logs}))
    xsv=(1-Y)/(1-Y*xi)
    val={k:sp.cancel(pieces[n].as_expr().subs(x,(xsv if p is xs else p))) for k,(n,p) in at.items()}
    target={'1':co['1'],'LY':co['LY'],'Lxi':co['Lxi'],'L1Y':0,'L1xi':0,'LA':co['LA'],'LB':co['LB']}
    for k,c in coefs.items():
        d=sp.cancel(sp.together(c.subs(val).subs(xs,xsv)-target[k]))
        print(k,'ok' if d==0 else 'FAIL', flush=True)
    def lean(e):
        s=sp.sstr(e,order='lex').replace('**',' ^ ').replace('*',' * ')
        for k in sorted(at,key=len,reverse=True):
            n,p=at[k]; ps={0:'0',1:'1'}.get(p,'(xStar Y ξ)') if p is not xs else '(xStar Y ξ)'
            s=s.replace(k,f'c{n} Y ξ {ps}')
        s=s.replace('xs','xStar Y ξ')
        return s
    out=[]
    names={'1':'cφ1','LY':'cφY','Lxi':'cφx','LA':'cφA','LB':'cφB','L1Y':None,'L1xi':None}
    for k,c in coefs.items():
        if c==0: continue
        tgt=names[k] and f'{names[k]} Y ξ' or '0'
        st=lean(c)
        used=[d for d in ['xStar','cA1','cQ1x','cC1','cA2','cC2a','cC2b'] if d+' ' in st]
        UNF=', '.join(used+['px']+([names[k]] if names[k] else []))
        out.append(f"""theorem cornerF_coeff_{k} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hξ2 : ξ ≠ 1 / 2) :
        {lean(c)} = {tgt} := by
      obtain ⟨hY0, hY1⟩ := hY
      obtain ⟨hξ0, hξ1⟩ := hξ
      have hA : 1 - Y * ξ ≠ 0 := by nlinarith
      have hY1' : Y - 1 ≠ 0 := by linarith
      have hξ1' : ξ - 1 ≠ 0 := by linarith
      have hξ2' : 2 * ξ - 1 ≠ 0 := fun h => hξ2 (by linarith)
      have hξ2'' : ξ * 2 - 1 ≠ 0 := fun h => hξ2 (by linarith)
      have := hY0.ne'
      have := hξ0.ne'
      simp only [{UNF}]
      first
      | (field_simp; done)
      | (field_simp; ring)
    """)
    lc=' +\n    '.join([f'({l}) * cornerF_coeff_{k} hY hξ hξ2' for k,l,_ in logs if coefs[k]!=0]+['cornerF_coeff_1 hY hξ hξ2'])
    open('xends.lean.block','w').write(XI.wrapall('\n'.join(out)))
    open('xends_lc.txt','w').write(lc)
    print(open('xends.lean.block').read()[:4000])


STAGES['endpoints'] = stage_endpoints

def stage_lean_defs():
    """emits the data of UnitSCCornerXDefs.lean (xdefs.lean.block, xderiv.lean.block)."""
    import sys, pickle
    sys.path.insert(0, CROSSED)
    import xi_integration as XI
    import sympy as sp
    Y,xi,x=sp.symbols('Y xi x',positive=True)
    CW,CB,R1,R2=pickle.load(open('xgen.pkl','rb'))
    pieces,Aa,Bb,poly=pickle.load(open('xanti.pkl','rb'))
    co=pickle.load(open('phico.pkl','rb'))
    def lr(e): return XI.lean_rat(sp.sympify(e))
    out=[]
    Kx=sp.factor(sp.cancel(-CB/x))
    def deflean(name,args,body,doc):
        out.append(f"/-- {doc} -/\nnoncomputable def {name} ({args} : ℝ) : ℝ :=\n  {body}\n")
    deflean('cKx','Y ξ x',lr(Kx),'`K/x`, with `K` the coefficient of `log(1 + M/(β h))` at `λ = 0`.')
    deflean('cR1','Y ξ x',lr(R1),'The rational part of `G_C` on the branch `x < x*`.')
    # cR2 itself is defined in Lean as cR2N/((1 - xi x)(1 - (1 - xi) x)), cR2N from stage terms_branch2
    def pxdef(name,P,doc):
        cs=P.all_coeffs()[::-1]; cs=cs+[0]*(7-len(cs))
        al='\n'.join('    '+lr(c) for c in cs)
        alD='\n'.join('    '+lr(c) for c in cs[1:])
        out.append(f"/-- {doc} -/\nnoncomputable def {name} (Y ξ x : ℝ) : ℝ :=\n  px\n{al}\n    x\n\n/-- The `x`-derivative of `{name}`. -/\nnoncomputable def {name}D (Y ξ x : ℝ) : ℝ :=\n  pxD\n{alD}\n    x\n\ntheorem hasDerivAt_{name} (Y ξ x : ℝ) : HasDerivAt ({name} Y ξ) ({name}D Y ξ x) x :=\n  hasDerivAt_px _ _ _ _ _ _ _ x\n")
    docs=dict(A1='The rational part of the antiderivative on `x < x*`.',Q1x='The coefficient of `x log x` (and, times `x`, of `log ξ + log(1 - Y)`) in the antiderivative.',
      C1='The coefficient of `log(Y + ξ(1 - Y) x)` in the antiderivative on `x < x*`.',A2='The rational part of the antiderivative on `x > x*`.',
      C2a='The coefficient of `log(1 - ξ x)` in the antiderivative on `x > x*`.',C2b='The coefficient of `log(1 - (1 - ξ) x)` in the antiderivative on `x > x*`.')
    for k in ['A1','Q1x','C1','A2','C2a','C2b']:
        pxdef('c'+k,pieces[k],docs[k])
    names={'1':'cφ1','LY':'cφY','Lxi':'cφx','LA':'cφA','LB':'cφB'}
    dd={'1':'rational part','LY':'coefficient of `log Y`','Lxi':'coefficient of `log ξ`','LA':'coefficient of `log(1 - Y ξ)`','LB':'coefficient of `log(ξ + Y - 2Yξ)`'}
    for k,n in names.items():
        deflean(n,'Y ξ',lr(co[k]),f'The {dd[k]} of `Φ_C(Y, ξ)` (eq. (6.7)).')
    open('xdefs.lean.block','w').write(XI.wrapall('\n'.join(out)))
    print(XI.wrapall('\n'.join(out))[:3000])
    # derivative identities
    D=[]
    D.append("""theorem cQ1x_deriv {Y ξ x : ℝ} (hY0 : Y ≠ 0) :
        cQ1x Y ξ x + x * cQ1xD Y ξ x = -(x * cKx Y ξ x) := by
      unfold cQ1x cQ1xD cKx px pxD
      field_simp
      ring
    """)
    for n in ['C1','C2a','C2b']:
        D.append(f"""theorem c{n}_deriv {{Y ξ x : ℝ}} (hY0 : Y ≠ 0) :
        c{n}D Y ξ x = x * cKx Y ξ x - (1 - x) / 2 := by
      unfold c{n}D cKx pxD
      field_simp
      ring
    """)
    D.append("""theorem cA1_deriv {Y ξ x : ℝ} (hY0 : 0 < Y) (hY1 : Y < 1) (hξ0 : 0 < ξ) (hx : 0 < x) :
        cA1D Y ξ x + cQ1x Y ξ x + cC1 Y ξ x * (ξ * (1 - Y) / (Y + ξ * (1 - Y) * x)) = cR1 Y ξ x := by
      have h1Y : 0 < 1 - Y := by linarith
      have hW : Y + ξ * (1 - Y) * x ≠ 0 := by positivity
      have hY1' : Y - 1 ≠ 0 := by linarith
      have := hY0.ne'
      have := hξ0.ne'
      unfold cA1D cQ1x cC1 cR1 px pxD
      field_simp
      ring
    """)
    open('xderiv.lean.block','w').write('\n'.join(D))


STAGES['lean_defs'] = stage_lean_defs

def stage_split_branch2():
    """partial fractions of cR2 (UnitSCCornerXRat.lean): exact; emits xsplit.lean.block."""
    import sys, pickle
    sys.path.insert(0, CROSSED)
    import xi_integration as XI
    import sympy as sp
    Y,xi,x=sp.symbols('Y xi x',positive=True)
    CW,CB,R1,R2=pickle.load(open('xgen.pkl','rb'))
    pieces,Aa,Bb,poly=pickle.load(open('xanti.pkl','rb'))
    DOM=sp.QQ.frac_field(Y,xi)
    P=lambda e: sp.Poly(sp.cancel(e),x,domain=DOM)
    lr=lambda e: XI.lean_rat(sp.sympify(e))
    C2a=pieces['C2a']; C2b=pieces['C2b']
    # C2a*(-xi) - Aa = -(1-xi x) Ta
    Ta,ra=sp.div(P(C2a.as_expr()*xi+Aa),P(1-xi*x)); assert ra.is_zero
    Tb,rb=sp.div(P(C2b.as_expr()*(1-xi)+Bb),P(1-(1-xi)*x)); assert rb.is_zero
    P2=P(poly)
    A2=pieces['A2']; Q1x=pieces['Q1x']
    chk=sp.cancel(sp.diff(A2.as_expr(),x)+(1-x)/4+2*Q1x.as_expr()-Ta.as_expr()-Tb.as_expr()-P2.as_expr())
    print('poly identity', chk==0)
    print('R2 split', sp.cancel(R2-(P2.as_expr()+Aa/(1-xi*x)+Bb/(1-(1-xi)*x)))==0)
    out=[]
    def pxdef(name,Pp,doc):
        cs=Pp.all_coeffs()[::-1]; cs=cs+[0]*(7-len(cs))
        al='\n'.join('    '+lr(c) for c in cs)
        out.append(f"/-- {doc} -/\nnoncomputable def {name} (Y ξ x : ℝ) : ℝ :=\n  px\n{al}\n    x\n")
    pxdef('cP2',P2,'The polynomial part of `cR2`.')
    pxdef('cTa',Ta,'`(ξ cC2a + cAa)/(1 - ξ x)`, a polynomial.')
    pxdef('cTb',Tb,'`((1 - ξ) cC2b + cBb)/(1 - (1 - ξ) x)`, a polynomial.')
    out.append(f"/-- The residue of `cR2` at `x = 1/ξ`, times `1 - ξ x`. -/\nnoncomputable def cAa (Y ξ : ℝ) : ℝ :=\n  {lr(Aa)}\n")
    out.append(f"/-- The residue of `cR2` at `x = 1/(1 - ξ)`, times `1 - (1 - ξ) x`. -/\nnoncomputable def cBb (Y ξ : ℝ) : ℝ :=\n  {lr(Bb)}\n")
    open('xsplit.lean.block','w').write(XI.wrapall('\n'.join(out)))
    print(len(open('xsplit.lean.block').read()))


STAGES['split_branch2'] = stage_split_branch2

def stage_terms_branch2():
    """the five terms of cFormR on x > x* times (1 - xi x)(1 - (1 - xi) x) (UnitSCCornerXDefs.lean): exact; emits xbr2.lean.block."""
    import sys, pickle
    sys.path.insert(0, CROSSED)
    import xi_integration as XI
    import sympy as sp
    Y,xi,x=sp.symbols('Y xi x',positive=True)
    CW,CB,R1,R2=pickle.load(open('xgen.pkl','rb'))
    y3=Y*xi; y4=Y*(1-xi)
    p1=(2*x**3*y3**2 - 2*x**3*y3 - 6*x**2*y3**2 - 4*x**2*y3*y4 + 6*x**2*y3 + 2*x**2*y4 - x**2
        + 6*x*y3**2 + 8*x*y3*y4 - 6*x*y3 + 2*x*y4**2 - 6*x*y4 - 2*y3**2 - 4*y3*y4 + 4*y3 - 2*y4**2 + 4*y4)
    p2=(8*x**2*y3**2 - 8*x**2*y3 - 10*x*y3**2 - 4*x*y3*y4 + 2*x*y3 - 2*x*y4 + 5*x + 2*y3**2
        + 4*y3 - 2*y4**2 + 4*y4 - 4)
    g=y3*(1-y3-y4); q=x*(2-x)*(1-2*y3); r=3*x*(1-2*y3)
    a0=x/4*p1; a1=x/4*g*(q-p1); a2=-(x/4*q*g**2)
    c2=x/4*g*(r+p2); c3=-(x/4*r*g**2)
    M=Y**2; h=x; be=y3*y4*x/(1-x)
    AB=(1-xi*x)*(1-(1-xi)*x)
    ts=[a0/(h*(M+be*h)), -a1/(M*(M+be*h)), a2*(1/(M**2*be)+h/(M**2*(M+be*h))), c2/(M*be), c3*(1/(2*M*be**2)-h/(M**2*be))]
    DOM=sp.QQ.frac_field(Y,xi)
    qs=[sp.Poly(sp.cancel(t*AB),x,domain=DOM) for t in ts]
    N=sum(q.as_expr() for q in qs)
    assert sp.cancel(N/AB-R2)==0
    NP=sp.Poly(sp.cancel(N),x,domain=DOM)
    print([q.degree() for q in qs], NP.degree())
    lr=lambda e: XI.lean_rat(sp.sympify(e))
    def pxs(Pp):
        cs=Pp.all_coeffs()[::-1]; cs=cs+[0]*(7-len(cs))
        return 'px\n'+'\n'.join('    '+lr(c) for c in cs)+'\n    x'
    out=[f"/-- The numerator of `cR2` over `(1 - ξ x)(1 - (1 - ξ) x)`. -/\nnoncomputable def cR2N (Y ξ x : ℝ) : ℝ :=\n  {pxs(NP)}\n"]
    for i,qq in enumerate(qs):
        out.append(f"/-- The `{i+1}`-th term of `cFormR` on the branch `x > x*`, times `(1 - ξ x)(1 - (1 - ξ) x)`. -/\nnoncomputable def cR2q{i+1} (Y ξ x : ℝ) : ℝ :=\n  {pxs(qq)}\n")
    open('xbr2.lean.block','w').write(XI.wrapall('\n'.join(out)))
    print(len(open('xbr2.lean.block').read()))


STAGES['terms_branch2'] = stage_terms_branch2

def stage_xi_letters():
    """Y Phi_C in the letters of section 4.5.2; the xi-antiderivative of xi_integration.py."""
    import sys, pickle, time
    sys.path.insert(0, CROSSED)
    import xi_integration as XI
    import sympy as sp
    Y,x=XI.Y,XI.x     # x is xi here
    co0=pickle.load(open('phico.pkl','rb'))
    Ys,xis=sp.symbols('Y xi',positive=True)
    sub={Ys:Y, xis:x}
    m={'1':'1','LY':'Y','Lxi':'x','LA':'A','LB':'B'}
    co={m[k]:sp.factor(sp.cancel(Y*sp.sympify(v).subs({s:sub[s] for s in sp.sympify(v).free_symbols if s.name in('Y','xi')}))) for k,v in co0.items() if k in m}

    for k,v in co.items(): print(k, sp.fraction(v)[1])
    t0=time.time()
    coef,dil=XI.antiderivative(co)
    p={k:XI.pf(v) for k,v in coef.items()}
    print('slots ok', all(set(v)<=set(XI.SLOTS) for v in p.values()))
    for k,v in dil.items(): print('dil',k,':',v)
    cL=XI.find_dil(dil,Y*x); cq=XI.find_dil(dil,1-x)
    print('cq-checks', sp.cancel(XI.find_dil(dil,-Y*(1-x)/(1-Y))-cq)==0, sp.cancel(XI.find_dil(dil,(1-2*Y)*(1-x)/(1-Y))+cq)==0)
    cD=XI.find_dil(dil,(2*Y-1)*x/Y)
    print('cL',cL,' cq',cq,' cD',cD)
    for k,v in p.items():
        print(k,{s:sp.factor(c) for s,c in v.items()})
    pickle.dump((co,coef,dil,p,cL,cq,cD),open('xistep.pkl','wb'))
    print(time.time()-t0)


STAGES['xi_letters'] = stage_xi_letters


def main():
    if len(sys.argv) != 2:
        sys.exit('usage: corner_integration.py OUTDIR')
    outdir = os.path.abspath(sys.argv[1])
    os.makedirs(outdir, exist_ok=True)
    os.chdir(outdir)
    for name, f in STAGES.items():
        print(f'== {name}', flush=True)
        f()
    print('== xi-integration (corner_xi_integration.py)', flush=True)
    sys.argv = [os.path.join(HERE, 'corner_xi_integration.py'), '--emit', os.path.join(outdir, 'xiblocks')]
    runpy.run_path(sys.argv[0], run_name='__main__')


if __name__ == '__main__':
    main()
