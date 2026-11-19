import sympy as sp, pickle, re
exec(open('gen1lean.py').read().split("out=[]")[0])
exec(open('wraplib.py').read())
H,rho,K,pref=pickle.load(open('gen1.pkl','rb'))
ms=sorted(H.keys(), reverse=True)
x=u
LA=['log x','log (1 - x)','log (1 + x)','Li 2 x','Li 2 (-x)']
def wrapall(txt):
    out=[]
    for ln in txt.split('\n'): out+=wrap(ln)
    return '\n'.join(out)
def monlean(m,var='x'):
    fs=[]
    for e,s in zip(m,LA):
        s=s.replace('x',var)
        if e==1: fs.append(s)
        elif e>1: fs.append(f'{s} ^ {e}')
    return ' * '.join(fs)
# ---------- limit at 0
a,s1,sm,sP,sQ=sp.symbols('a s1 sm sP sQ')
hs={m:sp.Symbol('h'+nm(m)) for m in ms}
L1=-u-u**2/2+u**3*s1; Lm=u-u**2/2+u**3*sm; P2=u*sP; M2=-u*sQ
Gs=sp.expand(sum(hs[m]*a**m[0]*L1**m[1]*Lm**m[2]*P2**m[3]*M2**m[4] for m in ms))
Gr=sp.expand(sum(H[m]*a**m[0]*L1**m[1]*Lm**m[2]*P2**m[3]*M2**m[4] for m in ms))
PS=sp.Poly(Gs,a,s1,sm,sP,sQ).as_dict(); PR=sp.Poly(Gr,a,s1,sm,sP,sQ).as_dict()
RN=['remL1','remLm','remP','remM']
def Bfactors(M):
    fs=[]
    for e,nmx in zip(M[1:],RN): fs+= [nmx]*e
    return fs
def mname(M): return ''.join(map(str,M))
defs=[]; ids=[]; terms=[]; lc=[]
mons0=sorted(PS.keys(),reverse=True)
def lean_coef(e):
    e=sp.expand(e)
    parts=[]
    for t in sp.Add.make_args(e):
        c,r=t.as_coeff_Mul()
        fs=[]
        for f in sp.Mul.make_args(r):
            if f==1: continue
            b,ex=f.as_base_exp()
            bs=str(b)
            if bs.startswith('h'): bs=f'{bs} x'
            elif bs=='u': bs='x'
            fs.append(bs if ex==1 else f'{bs} ^ {ex}')
        cs = str(abs(c)) if abs(c)!=1 or not fs else ''
        if '/' in cs: cs=f'({cs})'
        body=' * '.join(([cs] if cs else [])+fs)
        parts.append(('-' if c<0 else '+', body))
    s=''
    for i,(sg,b) in enumerate(parts):
        if i==0: s = b if sg=='+' else f'-{b}' if ' ' not in b else f'-({b})'
        else: s+=f' {sg} {b}'
    return s if s else '0'
for M in mons0:
    cR=sp.factor(sp.together(PR[M]))
    if not any(M):
        defs.append(f'/-- The constant-monomial coefficient of `G₁` near `0`. -/\nnoncomputable def c0fun (x : ℝ) : ℝ :=\n  {rat_lean(cR)}\n')
        ids.append((M,lean_coef(PS[M]),'c0fun x',['c0fun']))
        continue
    dM=sp.factor(cR/u)
    defs.append(f'/-- Coefficient `{mname(M)}` of `G₁` near `0`, divided by `x`. -/\nnoncomputable def d{mname(M)} (x : ℝ) : ℝ :=\n  {rat_lean(dM)}\n')
    ids.append((M,lean_coef(PS[M]),f'x * d{mname(M)} x',[f'd{mname(M)}']))
src=[]
src.append('\n'.join(defs))
# term expressions
def xl(j): return {0:'x',1:'(x * log x)',2:'(x * log x ^ 2)'}[j]
def Bexpr(M):
    fs=Bfactors(M); return ' * '.join(f'{f} x' for f in fs)
rhs=['c0fun x']
for M in mons0:
    if not any(M): continue
    t=f'd{mname(M)} x * {xl(M[0])}'
    if Bfactors(M): t=f'{t} * ({Bexpr(M)})'
    rhs.append(t)
src.append(f'''theorem setAG1_eq_near_zero {{x : ℝ}} (hx : x ∈ Ioo (0 : ℝ) 1) :
    setAG1 x = {(" +" + chr(10) + "      ").join(rhs)} := by
  obtain ⟨h0, h1⟩ := hx
  have hz : x ≠ 0 := h0.ne'
  have hp : 1 + x ≠ 0 := by linarith
  have hL1 : log (1 - x) = -x - x ^ 2 / 2 + x ^ 3 * remL1 x := by
    unfold remL1; field_simp; ring
  have hLm : log (1 + x) = x - x ^ 2 / 2 + x ^ 3 * remLm x := by
    unfold remLm; field_simp; ring
  have hP : Li 2 x = x * remP x := by unfold remP; field_simp
  have hM : Li 2 (-x) = -x * remM x := by unfold remM; field_simp''')
for j,(M,cl,cr,used) in enumerate(ids):
    hu=sorted(set(re.findall(r'\b(h\d{5})\b',cl)))
    src.append(f'  have e{j} : {cl} = {cr} := by\n    simp only [{", ".join(hu+used)}]\n    field_simp\n    ring')
src.append('  unfold setAG1\n  rw [hL1, hLm, hP, hM]')
def Mmon(M):
    fs=[]
    if M[0]==1: fs.append('log x')
    elif M[0]>1: fs.append(f'log x ^ {M[0]}')
    fs+= [f'{f} x' for f in Bfactors(M)]
    return ' * '.join(fs)
src.append('  linear_combination '+' + '.join((f'{Mmon(M)} * e{j}' if any(M) else f'e{j}') for j,(M,_,_,_) in enumerate(ids)))
# limit theorem at 0
lim=[]
lim.append('''/-- `G₁(0⁺) = -4619/432`. -/
theorem tendsto_setAG1_zero : Tendsto setAG1 (𝓝[>] 0) (𝓝 (-(4619 / 432))) := by
  have ev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have b1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), |remL1 x| ≤ 3 := ev.mono fun x hx => abs_remL1_le hx.1 hx.2
  have bm : ∀ᶠ x in 𝓝[>] (0 : ℝ), |remLm x| ≤ 3 := ev.mono fun x hx => abs_remLm_le hx.1 hx.2
  have bP : ∀ᶠ x in 𝓝[>] (0 : ℝ), |remP x| ≤ 3 := ev.mono fun x hx => abs_remP_le hx.1 hx.2
  have bM : ∀ᶠ x in 𝓝[>] (0 : ℝ), |remM x| ≤ 3 := ev.mono fun x hx => abs_remM_le hx.1 hx.2
  have x0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tlim hl (by fun_prop) rfl
  have x1 : Tendsto (fun x : ℝ => x * log x) (𝓝[>] 0) (𝓝 0) := tendsto_mul_log_zero
  have x2 : Tendsto (fun x : ℝ => x * log x ^ 2) (𝓝[>] 0) (𝓝 0) := tendsto_mul_log_sq_zero
  have cc := tlim hl (g := c0fun) (by unfold c0fun; fun_prop (disch := norm_num)) rfl''')
BN={'remL1':'b1','remLm':'bm','remP':'bP','remM':'bM'}
tnames=[]
for M in mons0:
    if not any(M): continue
    n=mname(M)
    lim.append(f'  have l{n} := tendsto_mul_zero_of_tendsto (tlim hl (g := d{n})\n    (by unfold d{n}; fun_prop (disch := norm_num)) rfl) x{M[0]}')
    fs=Bfactors(M)
    if fs:
        bcode=f'{BN[fs[0]]}'
        for f in fs[1:]:
            bcode=f'({bcode}.and {BN[f]}).mono fun _ h => abs_mul_le_three h.1 h.2'
            bcode=f'({bcode})'
        lim.append(f'  have t{n} := tendsto_mul_bdd l{n} {bcode}')
    else:
        lim.append(f'  have t{n} := l{n}')
    tnames.append(f't{n}')
code='cc'
for t in tnames: code=f'({code}.add {t})'
lim.append(f'  have H := {code}')
lim.append('''  have ev' : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have H2 : Tendsto setAG1 (𝓝[>] 0) (𝓝 _) := H.congr' <| by
    filter_upwards [ev'] with x hx
    rw [setAG1_eq_near_zero hx]
  convert H2 using 2
  simp only [c0fun]
  norm_num''')
src.append('\n'.join(lim))
# ---------- limit at 1
L1m=[m for m in ms if m[1]>0]
qdefs=[]
for m in L1m:
    Q=sp.factor(H[m]/(1-u))
    qdefs.append(f'/-- `h{nm(m)} / (1 - x)`. -/\nnoncomputable def q{nm(m)} (x : ℝ) : ℝ :=\n  {rat_lean(Q)}\n')
src.insert(0,'\n'.join(qdefs))
def rest(m):
    mm=list(m); mm[1]-=1; return tuple(mm)
rhs1=[]
for m in ms:
    if m[1]>0:
        r=monlean(rest(m))
        rhs1.append(f'q{nm(m)} x' + (f' * ({r})' if any(rest(m)) else '') + ' * ((1 - x) * log (1 - x))')
    else:
        rhs1.append(f'h{nm(m)} x' + (f' * ({monlean(m)})' if any(m) else ''))
one=[]
one.append(f'''theorem setAG1_eq_near_one {{x : ℝ}} (hx : x ∈ Ioo (0 : ℝ) 1) :
    setAG1 x = {(" +" + chr(10) + "      ").join(rhs1)} := by
  obtain ⟨h0, h1⟩ := hx
  have hz : x ≠ 0 := h0.ne'
  have hp : 1 + x ≠ 0 := by linarith''')
for m in L1m:
    one.append(f'  have e{nm(m)} : h{nm(m)} x = (1 - x) * q{nm(m)} x := by\n    simp only [h{nm(m)}, q{nm(m)}]\n    field_simp\n    ring')
one.append('  unfold setAG1\n  rw [' + ', '.join(f'e{nm(m)}' for m in L1m) + ']\n  ring')
one.append('''
/-- `G₁(1⁻) = -41π²/81 - 1927/432 + π² log 2/3`. -/
theorem tendsto_setAG1_one :
    Tendsto setAG1 (𝓝[<] 1) (𝓝 (-(41 / 81) * π ^ 2 - 1927 / 432 + π ^ 2 * log 2 / 3)) := by
  have ev : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
  have hl : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have m1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have mm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have sI := ev.mono fun u hu => mem_Icc.2 (abs_le.1 (PM.data_id hu.1 hu.2).2.1.le)
  have sA := ev.mono fun u hu => mem_Icc.2 (abs_le.1 (PM.data_neg hu.1 hu.2).2.1.le)
  have e0 : Tendsto (fun x : ℝ => log x) _ (𝓝 0) :=
    tlim hl (continuousAt_log one_ne_zero) (by norm_num)
  have em : Tendsto (fun x : ℝ => log (1 + x)) _ (𝓝 (log 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have qP := tendsto_Li_comp (k := 2) (by norm_num) m1
    (tlim hl (g := fun x : ℝ => x) (by fun_prop) rfl) sI
  have qM := tendsto_Li_comp (k := 2) (by norm_num) mm
    (tlim hl (g := fun x : ℝ => -x) (by fun_prop) (by norm_num)) sA
  have z : Tendsto (fun x : ℝ => (1 - x) * log (1 - x)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one''')
AN=['e0','e1X','em','qP','qM']
def chain(m):
    fs=[]
    for e,s in zip(m,AN):
        if e==1: fs.append(s)
        elif e>1: fs.append(f'({s}.pow {e})')
    if not fs: return None
    code=fs[0]
    for f in fs[1:]: code=f'({code}.mul {f})'
    return code
tn=[]
for i,m in enumerate(ms):
    if m[1]>0:
        base=f'(tlim hl (g := q{nm(m)}) (by unfold q{nm(m)}; fun_prop (disch := norm_num)) rfl)'
        ch=chain(rest(m))
        code= f'{base}.mul {ch}' if ch else base
        one.append(f'  have T{i} := ({code}).mul z')
    else:
        base=f'(tlim hl (g := h{nm(m)}) (by unfold h{nm(m)}; fun_prop (disch := norm_num)) rfl)'
        ch=chain(m)
        one.append(f'  have T{i} := {base}.mul {ch}' if ch else f'  have T{i} := {base}')
    tn.append(f'T{i}')
code=tn[0]
for t in tn[1:]: code=f'({code}.add {t})'
one.append(f'  have H := {code}')
hdefs=' '.join(f'h{nm(m)}' for m in ms if m[1]==0)
one.append(f'''  have H2 : Tendsto setAG1 (𝓝[<] 1) (𝓝 _) := H.congr' <| by
    filter_upwards [ev] with x hx
    rw [setAG1_eq_near_one hx]
  convert H2 using 2
  simp only [{", ".join(f"h{nm(m)}" for m in ms if m[1]==0)}, log_one, mul_zero, zero_mul,
    show Li 2 1 = π ^ 2 / 6 from Li₂_one, show Li 2 (-1) = -π ^ 2 / 12 from Li₂_neg_one]
  norm_num
  ring''')
src.append('\n'.join(one))
pickle.dump('\n\n'.join(src),open('limsrc.pkl','wb'))
open('limsrc.lean','w').write(wrapall('\n\n'.join(src)))
print(len(mons0))
