# Generates the endpoint expansions of setCG1 (SetCW1Lim) and setCJ (SetCJInt).
import sys
exec(open('common.py').read())
exec(open('expand.py').read())
R=sp.Rational
G=pickle.load(open('G.pkl','rb')); J=pickle.load(open('terms.pkl','rb'))
REM={0:['remA x','remB x','remC x','remD x'],1:['remA x','remA (x / 2)','remC x','remC (x * (2 - x))']}
BDD={0:['bdd_remA','bdd_remB','bdd_remC','bdd_remD'],1:['bdd_remA','bdd_remA_half','bdd_remC','bdd_remC_w']}
def numlean(q):
    return f'{q.p}' if q.q==1 else f'{q.p} / {q.q}'
def polylean(e,var,extra=()):
    """polynomial in y,l2,pi2 (and extra symbols -> lean strings) with rational coefficients"""
    gens=[y,l2,pi2]+[s for s,_ in extra]
    P=sp.Poly(sp.expand(e),*gens)
    terms=sorted(P.terms(),key=lambda t:(t[0][3:],t[0][:3]))
    out=[]
    for mon,c in terms:
        fs=[]
        k,b,cc=mon[:3]
        for (s,ls),ex in zip(extra,mon[3:]):
            if ex: fs.append(ls)
        if k: fs.append(var if k==1 else f'{var} ^ {k}')
        if b: fs.append('log 2' if b==1 else f'log 2 ^ {b}')
        if cc: fs.append('π ^ 2' if cc==1 else f'π ^ {2*cc}')
        c=sp.Rational(c); ac=abs(c)
        if fs:
            body=' * '.join(fs)
            s=body if ac==1 else f'{numlean(ac)} * {body}'
        else: s=numlean(ac)
        out.append(('-' if c<0 else '+',s))
    if not out: return '0'
    r=('-' if out[0][0]=='-' else '')+out[0][1]
    for sg,s in out[1:]: r+=f' {sg} {s}'
    return r
def ratlean(e,var):
    e=sp.cancel(sp.together(e))
    n,d=sp.fraction(e)
    c,fl=sp.factor_list(sp.Poly(d,y))
    parts=[]; sgn=1
    for f,k in fl:
        f=f.as_expr()
        for lin,lean in ((1-y,f'(1 - {var})'),(1+y,f'(1 + {var})'),(2-y,f'(2 - {var})')):
            q=sp.cancel(f/lin)
            if q.is_number:
                sgn*=q**k; parts.append(lean if k==1 else f'{lean} ^ {k}'); break
        else: raise Exception(f)
    c=c*sgn
    if c<0: n=-n; c=-c
    num=polylean(n,var)
    if c!=1: parts.insert(0,numlean(c))
    if not parts: return f'({num})'
    return f'({num}) / ({" * ".join(parts)})'
PRE={0:'''  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith''',1:'''  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith'''}
import os
NORING=set(eval(open('noring.txt').read())) if os.path.exists('noring.txt') else set()
def termlean(K,dname,end):
    j=K[0]; rs=[]
    for e,r in zip(K[1:],REM[end]):
        rs+= [r]*e
    rp=' * '.join(rs) if rs else '1'
    return f'{dname} x * log x ^ {j} * ({rp})'
def bddlean(K,end):
    bs=[]
    for e,b in zip(K[1:],BDD[end]): bs+=[b]*e
    if not bs: return 'bdd_one'
    code=bs[0]
    for b in bs[1:]: code=f'({code}.mul {b})'
    return code
def gen(F,fname,pref,end,const,var):
    hs={m:sp.Symbol(f'H{nm(m)}') for m in F}
    o=expand(F,end,hs)
    Ks=sorted(o,reverse=True)
    arg=var if end==0 else f'(1 - {var})'
    defs=[];eqs=[];terms=[];bds=[];lc=[]
    for i,K in enumerate(Ks):
        c,Es=o[K]
        dn=f'{pref}{"".join(map(str,K))}'
        isc = (K==(0,0,0,0,0))
        if const is not None:
            d=sp.cancel((c-(const if isc else 0))/y)
        else: d=c
        defs.append(f'/-- Expansion coefficient `{"".join(map(str,K))}` of `{fname}` at '
                    f'{"0" if end==0 else "1"}. -/\nnoncomputable def {dn} (x : ℝ) : ℝ :=\n  {ratlean(d,"x")}\n')
        extra=[(s,f'{s.name.replace("H","h" if fname=="setCG1" else "j")} {arg}') for s in hs.values()]
        lhs=polylean(Es,var,extra)
        used=sorted(set(re.findall(r'\b([hj]\d{5})\b',lhs)))
        if const is None: rhs=f'{dn} {var}'
        elif isc: rhs=f'{const_lean} + {var} * {dn} {var}'
        else: rhs=f'{var} * {dn} {var}'
        hyp0='(h0 : 0 < x) (h1 : x < 1)' if end==0 else '(h0 : 0 < y) (h1 : y < 1)'
        pre0=PRE[end]
        nr = '' if (pref,i) in NORING else '\n  ring'
        eqs.append(f'theorem {pref}_e{i} {{{var} : ℝ}} {hyp0} :\n    {lhs} = {rhs} := by\n{pre0}\n  simp only [{", ".join(used+[dn])}]\n  field_simp{nr}\n')
        terms.append(termlean(K,dn,end))
        rs=[]
        for e,r in zip(K[1:],REM[end]): rs+=[r.replace('x',var)]*e
        mon=([f'log {var} ^ {K[0]}'] if K[0] else [])+rs
        lc.append(' * '.join(mon+[f'({pref}_e{i} h0 h1)']))
        bds.append(f'  have t{i} := logSqBound_term (d := {dn}) (bddC fun x hx => by\n'
                   f'    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]\n'
                   f'    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]\n'
                   f'    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]\n'
                   f'    unfold {dn}; fun_prop (disch := simp [*])) {bddlean(K,end)} (j := {K[0]}) (by norm_num)')
    return Ks,defs,eqs,terms,bds,lc
which=sys.argv[1]
if which=='G':
    F=G; fname='setCG1'
else:
    F=J; fname='setCJ'
out=[]
for end in (0,1):
    pref=('g' if which=='G' else 'j')+('z' if end==0 else 'o')
    var='x' if end==0 else 'y'
    if which=='G':
        const = R(2147,432) if end==0 else R(3509,432)-R(8,9)*l2
        const_lean = '2147 / 432' if end==0 else '(3509 / 432 - 8 / 9 * log 2)'
    else: const=None; const_lean=None
    Ks,defs,eqs,terms,bds,lc=gen(F,fname,pref,end,const,var)
    out+=defs
    S=' +\n    '.join(terms)
    sname=f'{pref}Sum'
    out.append(f'/-- The expansion of `{fname}` at {"0" if end==0 else "1"}. -/\nnoncomputable def {sname} (x : ℝ) : ℝ :=\n  {S}\n')
    if end==0:
        hyp='(h0 : 0 < x) (h1 : x < 1)'
        lhsf=f'{fname} x'
        pre=('''  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith''')
        rw=('  rw [log_one_sub_eq h0, log_one_add_eq h0, Li_two_neg_eq h0, Li_two_eq h0]')
    else:
        hyp='(h0 : 0 < y) (h1 : y < 1)'
        lhsf=f'{fname} (1 - y)'
        pre=('''  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  have hw : 0 < y * (2 - y) := by nlinarith''')
        rw=('''  rw [show 1 - (1 - y) = y by ring, Li_two_neg_one_sub_eq h0 h1, Li_two_one_sub_eq h0 h1,
    log_two_sub_eq h0 h1, log_one_sub_eq h0, Li_two_eq h0, Li_two_eq hw]''')
    rhs = f'{sname} {var}' if which=='J' else f'{const_lean} + {var} * {sname} {var}'
    out+=eqs
    out.append(f'''theorem {fname}_eq_near_{"zero" if end==0 else "one"} {{{var} : ℝ}} {hyp} :
    {lhsf} = {rhs} := by
{pre}
  unfold {fname} {sname}
{rw}
  linear_combination ''' + ' + '.join(lc) + '\n')
    tsum='t0'
    for i in range(1,len(Ks)): tsum=f'({tsum}.add t{i})'
    out.append(f'''theorem logSqBound_{sname} : LogSqBound {sname} := by
  have bddC := @Bdd.of_continuousAt
''' + '\n'.join(bds) + f'''
  exact {tsum}
''')
open(f'lim{which}.lean','w').write(wrapall('\n'.join(out)))
