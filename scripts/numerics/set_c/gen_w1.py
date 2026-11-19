exec(open('common.py').read())
G=pickle.load(open('G.pkl','rb'))
J=pickle.load(open('terms.pkl','rb'))
g3terms=pickle.load(open('g3terms.pkl','rb'))
R=sp.Rational
# w_n : coefficients of setCg3 + 5/3 log u Phi/u
W={}
def addW(m,c): W[m]=sp.cancel(W.get(m,0)+c)
for a,m,c in g3terms: addW(m, c/(u-a))
for m,c in [((2,1,0,0,0),R(5,3)),((2,0,1,0,0),R(10,3)),((1,0,0,1,0),R(10,3)),((1,0,0,0,1),R(20,3))]:
    addW(m,c/u)
ms=sorted(G,reverse=True)
def e(i):
    v=[0]*5; v[i]=1; return tuple(v)
def sub(m,i):
    v=list(m); v[i]-=1; return tuple(v)
def addt(a,b): return tuple(x+y for x,y in zip(a,b))
DL=['u⁻¹','(1 - u)⁻¹','(1 + u)⁻¹']
dsym=[1/u,-1/(1-u),1/(1+u)]
# derivative contributions: n -> list of (sympy coef multiplier of H_m, lean string)
contrib={}
def addc(n,mname,factor_sym,lean):
    contrib.setdefault(n,[]).append((mname,factor_sym,lean))
for m in ms:
    for i,k in enumerate(m):
        if k==0: continue
        base=sub(m,i)
        kk='' if k==1 else f'{k} * '
        if i<3:
            sg='-' if i==1 else ''
            addc(base,m,k*dsym[i],f'{sg}{kk}h{nm(m)} u * {DL[i]}')
        else:
            n=addt(base,e(1 if i==3 else 2))
            addc(n,m,-k/u,f'-{kk}h{nm(m)} u * u⁻¹')
allmons=sorted(set(ms)|set(contrib)|set(J)|set(W),reverse=True)
checks=[]
for n in allmons:
    lhs_sym=(sp.diff(G[n],u) if n in G else 0)+sum(f*G[m] for m,f,_ in contrib.get(n,[]))
    rhs_sym=J.get(n,0)-W.get(n,0)
    assert sp.simplify(lhs_sym-rhs_sym)==0, n
    parts=([f'hd{nm(n)} u'] if n in G else [])+[l for _,_,l in contrib.get(n,[])]
    lhs=' + '.join(parts) if parts else '0'
    lhs=lhs.replace('+ -','- ')
    rparts=([f'j{nm(n)} u'] if n in J else [])+([f'- w{nm(n)} u'] if n in W else [])
    rhs=' '.join(rparts) if rparts else '0'
    if rhs.startswith('- '): rhs='-'+rhs[2:]
    used=sorted(set(re.findall(r'\b(h\d{5}|hd\d{5}|j\d{5}|w\d{5})\b',lhs+' '+rhs)))
    checks.append((n,lhs,rhs,used))
out=[]
for m in ms:
    out.append(f'/-- Coefficient of the monomial `{nm(m)}` in `G₁`. -/\nnoncomputable def h{nm(m)} (x : ℝ) : ℝ :=\n  {rat_lean(G[m])}\n')
    out.append(f'/-- Derivative of `h{nm(m)}`. -/\nnoncomputable def hd{nm(m)} (x : ℝ) : ℝ :=\n  {rat_lean(sp.diff(G[m],u))}\n')
for n in sorted(W,reverse=True):
    out.append(f'/-- Coefficient of `{nm(n)}` in `g₃ + (5/3) log x Φ(x)/x`. -/\nnoncomputable def w{nm(n)} (x : ℝ) : ℝ :=\n  {rat_lean(W[n])}\n')
def den_code(c,a,b,mm):
    fs=[]
    if a: fs.append("(hasDerivAt_id' u)" if a==1 else f'(hasDerivAt_pow {a} u)')
    if b: fs.append("((hasDerivAt_id' u).const_add 1)" if b==1 else f"(((hasDerivAt_id' u).const_add 1).pow {b})")
    if mm: fs.append("((hasDerivAt_id' u).const_sub 1)" if mm==1 else f"(((hasDerivAt_id' u).const_sub 1).pow {mm})")
    code=fs[0]
    if c!=1: code=f'({code}.const_mul ({c} : ℝ))'
    for f in fs[1:]: code=f'({code}.mul {f})'
    return code
for m in ms:
    P,c,a,b,mm=frac_parts(G[m])
    nf=sum(1 for z in (a,b,mm) if z)
    lem=[]
    if b>1 or mm>1: lem.append('Pi.pow_apply')
    if nf>1: lem.append('Pi.mul_apply')
    simpl=f"simp only [{', '.join(lem)}]; " if lem else ''
    terms=sorted(P.terms(), key=lambda t:t[0][0])
    lem2=list(lem)
    if any(cc>0 for (_,),cc in terms[1:]): lem2.append('Pi.add_apply')
    if any(cc<0 for (_,),cc in terms[1:]): lem2.append('Pi.sub_apply')
    if terms[0][1]<0: lem2.append('Pi.neg_apply')
    simpl2=f"\n  simp only [{', '.join(lem2)}]" if lem2 else ''
    out.append(f'''theorem hasDerivAt_h{nm(m)} {{u : ℝ}} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h{nm(m)} (hd{nm(m)} u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := {poly_deriv_code(P)}.div
    {den_code(c,a,b,mm)}
    (by {simpl}positivity)
  refine h.congr_deriv ?_
  unfold hd{nm(m)}{simpl2}
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring
''')
wsum=' + '.join(f'w{nm(n)} u' + (f' * {monlean(n,"u")}' if any(n) else '') for n in sorted(W,reverse=True))
wdefs=' '.join(f'w{nm(n)}' for n in sorted(W,reverse=True))
out.append(f'''theorem setCg3_add_eq {{u : ℝ}} (hu : u ∈ Ioo (0 : ℝ) 1) :
    setCg3 u + setCw4 u = {wsum} := by
  obtain ⟨h0, h1⟩ := hu
  have hz : u ≠ 0 := h0.ne'
  have hm : u - 1 ≠ 0 := by linarith
  have hm' : 1 - u ≠ 0 := by linarith
  have hp : u + 1 ≠ 0 := by linarith
  have hp' : 1 + u ≠ 0 := by linarith
  unfold setCg3 setCw4 {wdefs}
  field_simp
  ring

end SetCW1

open SetCW1
''')
g1=' +\n    '.join(f'h{nm(m)} x' + (f' * ({monlean(m)})' if any(m) else '') for m in ms)
out.append(f'''/-- The rational-coefficient antiderivative `G₁`. -/
noncomputable def setCG1 (x : ℝ) : ℝ :=
  {g1}
''')
AN=['e0','e1','em','qP','qM']
def chain(m):
    fs=[]
    for k,s in zip(m,AN):
        if k==1: fs.append(s)
        elif k>1: fs.append(f'({s}.pow {k})')
    code=fs[0]
    for f in fs[1:]: code=f'({code}.mul {f})'
    return code
pr=['''/-- **The rational-coefficient part**: `G₁' = setCJ - g₃ - w₄` on `(0, 1)`. -/
theorem hasDerivAt_setCG1 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt setCG1 (setCJ u - setCg3 u - setCw4 u) u := by
  have hw := setCg3_add_eq hu
  obtain ⟨h0, h1⟩ := hu
  obtain ⟨di, ai, ni, li, -, gi1⟩ := PM.data_id h0 h1
  obtain ⟨dA, aA, nA, lA, -, gA1⟩ := PM.data_neg h0 h1
  obtain ⟨dB, -, nB, lB, -, -⟩ := PM.data_oneSub h0 h1
  have e0 := hasDerivAt_log_of di ni li
  have e1 := hasDerivAt_log_of dB nB lB
  have em : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + u)) u := by
    have := ((hasDerivAt_id' u).const_add 1).log (by linarith)
    simpa [one_div] using this
  have qP := hasDerivAt_Li_two_of di ai ni li gi1
  have qM := hasDerivAt_Li_two_of dA aA nA lA gA1''']
for i,m in enumerate(ms):
    if any(m): pr.append(f'  have t{i} := (hasDerivAt_h{nm(m)} h0 h1).mul {chain(m)}')
    else: pr.append(f'  have t{i} := hasDerivAt_h{nm(m)} h0 h1')
code='t0'
for i in range(1,len(ms)): code=f'({code}.add t{i})'
pr.append(f'  have h := {code}')
pr.append('  refine h.congr_deriv ?_')
pr.append('  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]')
pr.append("  have hp : 1 + u ≠ 0 := by linarith\n  have hm : 1 - u ≠ 0 := by linarith\n  have hz : u ≠ 0 := h0.ne'")
for j,(n,l,r,used) in enumerate(checks):
    pr.append(f'  have c{j} : {l} = {r} := by')
    pr.append(f'    simp only [{", ".join(used)}]')
    pr.append('    field_simp\n    ring')
pr.append('  unfold setCJ')
lc=' + '.join((f'{monlean(n,"u")} * c{j}' if any(n) else f'c{j}') for j,(n,_,_,_) in enumerate(checks))
pr.append(f'  linear_combination {lc} + hw')
out.append('\n'.join(pr))
body=wrapall('\n'.join(out))
open('w1body.lean','w').write(body)
print(len(checks), len(W))
