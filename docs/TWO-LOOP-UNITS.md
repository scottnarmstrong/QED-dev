# Two-loop units: low-dimensional integral representations of the q-type contributions

[Campaign HQ](../README.md) · [Two-loop derivation](TWO-LOOP-DERIVATION.md) ·
[Sources](SOURCES.md) · [Conventions](CONVENTIONS.md)

**Status (2026-11-18):** preparatory analysis for obligation O2-25 of
[TWO-LOOP-DERIVATION.md](TWO-LOOP-DERIVATION.md). Every representation below was derived from
the covariant Feynman-parametric integrand of section 11 of the derivation document and checked
numerically; the checks are evidence, not proof. The final one-dimensional (or master) integrals
are proved in Lean at helper level, as listed in the "Lean" paragraph below; the chain from the
model to these representations (section 8) is not proved. The verification script is
[`scripts/numerics/two_loop_unit_integrals.py`](../scripts/numerics/two_loop_unit_integrals.py).

Notation follows the derivation document: $r=\alpha/\pi$, $m=1$, photon mass $\lambda$
(called $m_\gamma$ there) on every photon line, Pauli–Villars photon mass $\Lambda$,
Feynman gauge, and every unit value is the coefficient of $r^2$ in $F_2$ at $q\to0$. The
units are those of section 5.2 of the derivation document:

| Unit | Content |
| --- | --- |
| L | ladder graph $+\ \delta_1$ at its external vertex $=\mathrm L_{\rm graph}+\delta_1F_2^{(2)}$ |
| X | crossed-ladder graph |
| S | $S_+ + S_-$ $+$ their $(\delta_2,\delta_m)$ insertions |
| C | $C_+ + C_-$ $+\ \delta_1$ at their internal vertices $=C_{+}+C_{-}+2\delta_1F_2^{(2)}$ |

The counterterms are the route-A on-shell ones: $\delta_2,\delta_m$ from the on-shell
electron conditions and $\delta_1$ from the charge condition, all with the Pauli–Villars
photon; $\delta_1=\delta_2$ (O2-15, proved).

## 1. Summary

| Unit | Representation of the limit $\lambda\to0$, $\Lambda\to\infty$ | Dimension, functions | Agreement with BMR-I p. 852 | Exact evaluation needs |
| --- | --- | --- | --- | --- |
| L | $\frac16+\int_0^1K_{\rm L}(Y)\,dY$, eq. (3.6) | 1D; rational, $\ln Y$, $\ln(1-Y)$ | 40 digits | $\mathrm{Li}_2(1)=\zeta(2)$ only (done by hand, 3.5) |
| S | $\ln\lambda+b_{\rm S}+o(1)$, $b_{\rm S}=2\int_0^1K_{\rm S}(Y)\,dY$, eq. (5.5) | 1D; rational, $\ln Y$, $\ln(1-Y)$ | 40 digits | $\mathrm{Li}_2(1)$ only (done by hand, 5.5) |
| C | $-\ln\lambda+b_{\rm C}+o(1)$, $b_{\rm C}=2\int G_{\rm C}-\frac32$, eq. (6.5); 1D form $2\int_0^1K_{\rm C}-\frac32$ (6.9) | 3D; rational and $\ln$ (2D with single logarithms after the $x$-integration, no $\mathrm{Li}_2$, 6.6.1) | 42 digits (1D form) | derived exactly in 6.6: $\zeta(2)\ln2$, $\zeta(3)$ through the masters of X; the 1D integral and its value proved in Lean |
| S$+$C | $b_{\rm S}+b_{\rm C}$: the logarithms cancel inside the counterterms, eq. (7.1) | 1D $+$ 1D (5.5), (6.9) | 42 digits (1D forms) | derived exactly (6.6.4); the 1D value proved in Lean |
| X | $\int_{\Delta_2}\Phi_{\rm X}(z_2,z_3)\,dz_2\,dz_3$, eq. (4.4); 1D form $\int_0^1K_{\rm X}$ (4.5) | 2D; rational and $\ln$ only (the $\mathrm{Li}_2$ terms of (4.3) have zero coefficient, 4.5) | 37 digits (1D form) | derived exactly in 4.5: $\zeta(2)\ln2$, $\zeta(3)$; master integrals proved in Lean |

Two findings are worth stating at the outset.

1. **Every route-A unit has exactly BMR's per-graph value**, including the separate finite
   parts of S and C: the route-A self-energy unit is $\ln\lambda+\frac{11}{24}-\frac13\zeta(2)
   +o(1)$, which is BMR-I p. 852 row b) to 40 digits, with the same photon-mass convention
   $\ln(\lambda/m)$. So the route-A allocation of counterterms (section 5.2 of the derivation
   document) coincides with BMR's ("every one-loop subgraph renormalized on shell").
   Section 11.4 of the derivation document found this to a few $10^{-5}$; here it is
   established to the precision of the representations.
2. **One structural identity drives all four reductions** (section 2): in hierarchical
   Cheng–Wu variables the two-loop $V$ function is the on-shell $V$ of the inner one-loop
   subgraph plus a shifted one-loop $V$ of the outer loop. It makes the integral over the
   outer electron parameter elementary for every graph.

**Lean (2026-11-18).** The exact values of the 1D integrals of L and S are proved at helper
level (`QED/TwoLoop/UnitLS.lean`: `integral_ladderKernel` $=\frac1{16}+\frac{\pi^2}{18}$,
`ladderUnit_value`, `integral_selfEnergyKernel` $=\frac{11}{48}-\frac{\pi^2}{36}$,
`selfEnergyUnit_finitePart_value`), with the integrability of both kernels. For C the 1D
integral is proved too (`QED/TwoLoop/UnitC.lean`: `intervalIntegrable_and_integral_cornerKernel`,
`cornerUnit_finitePart_value`, and `selfEnergyCornerUnit_value` for S + C
$=-\frac73+2\zeta(2)\ln2-\frac12\zeta(3)$). For X the 1D integral is proved too
(`QED/TwoLoop/UnitXKernel.lean`: `intervalIntegrable_and_integral_crossedKernel`,
`crossedUnit_value`, with the eight master integrals in `QED/Polylog/ExtraIntegrals.lean` and
`QED/TwoLoop/UnitX.lean`), including the endpoint limits of the boundary function and the
integrability of $K_{\rm X}$. The steps from the 2D representations to the 1D
kernels (the $x$- and $\xi$-integrations) are symbolic computations, and the link to the model
(section 8) is not proved.

**X link (2026-11-18).** The model's X unit is proved equal to an explicit iterated integral in
the hierarchical variables of section 2 (`QED/TwoLoop/UnitXGraph*.lean`,
`sixteen_pi_pow_four_mul_unitF2_X_eq_iterated`, at $m=e=1$, $0<m_\gamma<\Lambda$), whose $\lambda=0$,
$\Lambda=\infty$ term is exactly the integrand behind (4.1)/(4.4). The joint regulator limit is
proved by dominated convergence with a bound certified monomial by monomial (420 weighted AM–GM
certificates, kernel-checked), and the $w$- and $b$-integrations give $\Phi_{\rm X}$ in closed form
and (4.4) (`QED/TwoLoop/UnitXClose*.lean`). The X link now reduces to one statement, the
$\xi$-integration of 4.5.2 (`xUnitLimit_of_kernel`).

**S + C link, stage 1 (2026-11-18).** The pointwise trace identities and class-value formulas
are proved for S₊, S₋, C₊, C₋ (`QED/TwoLoop/UnitSCGraph*.lean`, `openZero_Sp_eq`, `openZero_Sm_eq`,
`openZero_Cp_eq`, `openZero_Cm_eq`, at $m=e=1$; C₋ from C₊ by charge-conjugation reversal at trace
level). **Stage 2 (reductions) is proved** (`QED/TwoLoop/UnitSCReduce*.lean`): explicit V, the
mirror identities S₋ = S₊ and C₋ = C₊ (by simplex permutations), integrability, merging, the
Pauli–Villars divided differences and Cheng–Wu, matched exactly to (5.1) and (6.2), and the unit
assembly with the δ₁ counterterm half of C. **The joint-limit risk is resolved**
(`QED/TwoLoop/UnitSCCloseIR.lean`, `selfVk_add_selfVm_add_oneLoopF2`): $V_k(\mu)+V_m(\mu)+
F_2^{(2)}(\mu)=0$ for every photon mass $\mu$, so the $(m^2/\Lambda^2)\ln m_\gamma$ terms of S and C
cancel exactly in S + C by $\delta_1=\delta_2$. Remaining: the δ₂/δ_m class values, the
$b$-integrations, the $\ln M_\Lambda$ cancellation, the uniform bounds and limit, and the $x$-, $\xi$-
integrations to the proved kernels.

## 2. The common starting point

### 2.1 The parametric integrand

For a graph $G$ with $N=6$ lines and two loops, section 11.1 of the derivation document
writes the $q\to0$ Pauli coefficient as an integral over the simplex of line parameters
(lines with equal routing merged into groups) of
$$f_G(z)=\frac{A_2(z)}{D(z)^2}+\frac{A_1(z)}{D(z)},\qquad
D=V(z)+\sum_{\text{photons}}z_i\,\mu_i,$$
where $\mu_i\in\{\lambda^2,\Lambda^2\}$ is the photon mass squared (each Pauli–Villars line is
a signed sum of the two), $V=J^{\mathsf T}U^{-1}J$ is the massless on-shell $V$ function
(AKN (55)–(57); CK-R (24)–(26)), $U=\det(U_{st})$, and $A_2,A_1$ are rational functions
obtained from the numerator algebra and the projector $P_2$ (CK-R rule 6; AKN (64)–(65)).
The overall divergence carries no $F_2$ part, so no $\ln D$ term occurs. The script
rebuilds $A_2,A_1$ in exact arithmetic from the numerator patterns of
`two_loop_units.py` and reproduces that script's integrand at random points.

$f_G$ is homogeneous of degree $-n$ in the $n$ group parameters, so the
**Cheng–Wu theorem** (standard; not in a pinned source) allows the simplex constraint to be
placed on any subset of parameters, the others running over $(0,\infty)$.

### 2.2 Hierarchical variables and the splitting identity

Choose the constraint on the parameters of the **inner** one-loop subgraph (the vertex or
self-energy subgraph that carries the subdivergence, or, for X, either loop), so that the
inner parameters lie on a simplex, and let the outer electron and photon parameters run
over $(0,\infty)$. Write $Y$ for the total inner electron parameter. Then, for each of the
four graphs, after the shift of the outer parameters given in the table,
$$U=b+w,\qquad D=M_{\rm in}+\frac{b^2}{b+w}+\lambda^2(w-e),\qquad
M_{\rm in}=Y^2+(1-Y)\,\mu_{\rm in}, \tag{2.1}$$
with $\mu_{\rm in}$ the mass squared of the inner photon:

| Graph | inner simplex | outer electron $b$ | outer photon $w$ | $g=\min b$ | $e=\min w$ |
| --- | --- | --- | --- | --- | --- |
| ladder | $z_B=Y$, $z_b=1-Y$ | $z_A+Y(1-Y)$ | $z_a$ | $Y(1-Y)$ | $0$ |
| $S_+$ | $z_3=Y$, $z_b=1-Y$ | $z_o+Y(1-Y)$ | $z_a$ | $Y(1-Y)$ | $0$ |
| $C_+$ | $(y_3,y_4,y_b)$, $Y=y_3+y_4$ | $z_o+y_3y_b$ | $z_a+y_3y_4$ | $y_3y_b$ | $y_3y_4$ |
| X | $(z_2,z_3,z_b)$, $Y=z_2+z_3$ | $z_1+z_2z_b$ | $z_a+z_2z_3$ | $z_2z_b$ | $z_2z_3$ |

(Line labels as in `two_loop_units.py`: $z_A,z_o,z_1$ outer electron group, $z_a$ outer
photon, $z_b$ inner photon.) Equation (2.1) was verified symbolically for each graph. Its
reading: $M_{\rm in}$ is the on-shell $V$ of the inner one-loop subgraph
($x^2+(1-x)\mu$ in the one-loop notation of section 6 of
[REGULARIZATION.md](REGULARIZATION.md)), and $b^2/(b+w)+\lambda^2w$ is the projective
one-loop $V$ of the outer loop, with its parameters shifted by $(g,e)$.

Finally put $w=b(1-x)/x$ with $x\in(0,1)$, the outer one-loop Feynman parameter (electron
fraction). Then $U=b/x$, the Jacobian is $b/x^2$, and
$$D=M_{\rm in}-\lambda^2e+b\,h(x),\qquad h(x)=\frac{x^2+(1-x)\lambda^2}{x}, \tag{2.2}$$
which is **linear in $b$**. With $A_2,A_1$ Laurent polynomials in $b$, the $b$-integral over
$b\ge\beta(x)$ is a combination of the elementary masters
$$I_{j,n}(\beta;M,h)=\int_\beta^\infty\frac{b^j\,db}{(M+bh)^n},\qquad n=1,2,\ j\le n-1,$$
with the logarithmic divergence of $I_{0,1}$ and $I_{1,2}$ at large $b$ removed (it cancels
between the two Pauli–Villars terms of the inner photon). For example
$I_{0,1}\to\frac1h\ln\frac{h}{M+\beta h}$,
$I_{1,2}\to\frac{1}{h^2}\bigl[\ln\frac{h}{M+\beta h}-\frac{M}{M+\beta h}\bigr]$,
$I_{-1,1}=\frac1M\ln\bigl(1+\frac M{\beta h}\bigr)$. The lower limit is $\beta=g$ for the
ladder and $S_+$; for $C_+$ and X the constraint $w\ge e$ gives
$\beta(x)=\max\bigl(g,\,ex/(1-x)\bigr)$, so the $x$-range splits at $x_*=g/(g+e)$.

### 2.3 Regulator limits used in every unit

- **Inner Pauli–Villars pair.** $D$ depends on the inner photon only through $M_{\rm in}$.
  As $\Lambda\to\infty$ the Pauli–Villars term contributes $-\ell(x)\ln M_\Lambda+e_0(x)$,
  with $M_\Lambda=Y^2+(1-Y)\Lambda^2$, $\ell$ the coefficient of the removed logarithm and
  $e_0=\ell\ln h-c_{1}/h^2$ ($c_1$ the coefficient of $b^1$ in $A_2$).
- **Counterterms at the same inner parameter.** Each counterterm is a one-loop integral over
  a Feynman parameter, which is identified with the inner $Y$ (or spread uniformly over the
  inner simplex at fixed $Y$). Then the $\ln M_\Lambda$ terms cancel **pointwise in the
  inner parameters**: for the vertex subgraphs $\ell=x(1-x)/(2h)$, so
  $\int_0^1\ell\,dx=\frac12F_2^{(2)}(\lambda)$ exactly, which is the coefficient carried by
  $\delta_1F_2^{(2)}$ at the same inner point; for S the analogous identity
  $\int_0^1\ell\,dx=\frac{1-Y}2V_k+V_m$ was checked numerically (to $10^{-16}$).
- **Outer Pauli–Villars pair.** The terms with the outer photon at mass $\Lambda$ vanish as
  $\Lambda\to\infty$; numerically they are $O(\Lambda^{-2})$ (for S: $3.8\times10^{-4}$ and
  $4.2\times10^{-6}$ at $\lambda=0.01$, $\Lambda=30,300$).

The resulting finite-$\lambda$, $\Lambda=\infty$ representations reproduce the
finite-regulator values of section 11 of the derivation document (tables below). They take
$\Lambda\to\infty$ before $\lambda\to0$; the joint limit used in packet T3 needs the
uniformity discussed in section 8.

## 3. The ladder unit L

### 3.1 Integrand

In the variables of section 2.2 ($a\equiv b$, $c=Y(1-Y)$, $U=a+z_a$),
$$f_{\rm L}=\frac{Y z_a(a-c)}{2U^4}\Bigl[\frac{9c+a}{D}+\frac{Q_0}{U D^2}\Bigr],\qquad
Q_0=(3Y-2)a^2+(4Y-Y^2-2)a z_a-2c\,z_a^2, \tag{3.1}$$
with $D=Y^2+(1-Y)\mu_{\rm in}+a^2/U+\lambda^2z_a$ and measure
$dY\,dz_A\,dz_a$, $Y\in(0,1)$, $z_A,z_a>0$. The factor $a-c=z_A$ is the weight of the merged
outer electron pair.

### 3.2 Counterterm in the inner parameter

From the parametric one-loop vertex (the script's `one_loop_vertex('F1')`),
$$\delta_1=-\int_0^1 dY\Bigl[\frac{Y(Y^2+2Y-2)}{2}\Bigl(\frac1{M_\lambda}-\frac1{M_\Lambda}\Bigr)
-\frac Y2\ln\frac{M_\lambda}{M_\Lambda}\Bigr],\qquad M_\mu=Y^2+(1-Y)\mu ,$$
and $F_2^{(2)}(\lambda)=\int_0^1\frac{x^2(1-x)}{x^2+(1-x)\lambda^2}dx$. The quantity $M_\mu$
coincides with $M_{\rm in}$ of (2.1), which is what makes the pointwise cancellation of
section 2.3 work.

### 3.3 Exact representation at finite $\lambda$, $\Lambda=\infty$

Doing the $a$-integral by the masters and combining with $\delta_1F_2^{(2)}$ at the same $Y$,
$$\mathrm L(\lambda)=\int_0^1\!dY\Bigl\{\int_0^1\!dx\,\frac{Yx(1-x)}2\Bigl[\frac{xq_0}{Mh}
-\frac{9c}{M}-\frac{\ln(M+ch)}{h}+\frac{Q}{M^2}\ln\Bigl(1+\frac{M}{ch}\Bigr)\Bigr]
-F_2^{(2)}(\lambda)\Bigl[\frac{Y(Y^2+2Y-2)}{2M}-\frac Y2\ln M\Bigr]\Bigr\}, \tag{3.4}$$
with $M=Y^2+(1-Y)\lambda^2$, $h=h(x)$ of (2.2), $\zeta=(1-x)/x$,
$q_0=(3Y-2)+(4Y-Y^2-2)\zeta-2c\zeta^2$ and $Q=c\,(8M+9ch-xq_0)$.

| $\lambda$ | (3.4), $\Lambda=\infty$ | section 11.4 ($\Lambda=1000$) |
| --- | --- | --- |
| $10^{-2}$ | $0.671406563$ | $0.671404$ (remainder $\approx+3\times10^{-6}$ to $\Lambda=\infty$) |
| $10^{-4}$ | $0.774977283$ | $0.774975$ |

### 3.4 The limit $\lambda\to0$

Two logarithms cancel: the bare ladder carries $+\frac12\ln\lambda$ from the region where the
**outer** photon is soft ($x\to0$), and $\delta_1F_2^{(2)}$ carries $-\frac12\ln\lambda$ from
the region where the **inner** photon is soft ($Y\to0$). The outer one is isolated by the
term
$$T_1=-\frac{Y c\,x(1-x)^3}{M\,(x^2+(1-x)\lambda^2)},\qquad
\iint T_1=\tfrac12\ln\lambda+\tfrac{11}{12}+o(1),$$
and the counterterm bracket integrates to $-F_2^{(2)}(\ln\lambda+\frac32)=-\frac12\ln\lambda
-\frac34+o(1)$. The remainder $R=G-T_1$ ($G$ the $x$-integrand of (3.4)) has a
$\lambda$-independent integrable limit $R_0(Y,x)$: it is a polynomial in $x$ times
$\ln x$, $\ln(1-Y)$, $\ln Y$ and $\ln(Y+(1-Y)x)$, divided by $Y^2$, with no $1/x$ left. Its
$x$-integral is elementary, and
$$\boxed{\ \mathrm L=\frac16+\int_0^1K_{\rm L}(Y)\,dY\ } \tag{3.6}$$
$$K_{\rm L}(Y)=\frac{(Y^3+3Y^2-2Y-2)\ln(1-Y)}{12Y^2}+\frac{(-7Y^3+11Y^2+Y-6)\ln Y}{12(1-Y)^2}
-\frac{23Y^3-41Y^2+16Y+4}{24Y(1-Y)} .$$
$K_{\rm L}$ is finite at $Y=1$ and behaves like $-\frac12\ln Y$ at $Y\to0$ (the $1/Y$ and
$1/(1-Y)$ poles cancel between terms).

**Numerics:** (3.6) gives $0.77747802228274214549080505554867506\ldots$; the difference from
BMR-I's $\frac{11}{48}+\frac13\zeta(2)$ is $5\times10^{-42}$ at 40-digit working precision.

### 3.5 Exact evaluation (by hand, checked)

Write $t=1-Y$. Splitting off the endpoint poles,
$$\int_0^1K_{\rm L}=\underbrace{\tfrac1{12}\!\int(Y+3)\ln(1-Y)}_{-5/16}
\underbrace{-\tfrac16\!\int\frac{\ln(1-Y)}{Y}}_{\zeta(2)/6}
\underbrace{-\tfrac16\!\int\Bigl[\frac{\ln(1-Y)}{Y^2}+\frac1Y\Bigr]}_{1/6}
\underbrace{-\tfrac1{12}\!\int\Bigl[\frac{\ln Y}{t^2}+\frac1t\Bigr]}_{1/12}
\underbrace{-\tfrac16\!\int\frac{\ln Y}{t}}_{\zeta(2)/6}
+\underbrace{\tfrac1{12}\!\int(-3-7Y)\ln Y}_{19/48}
\underbrace{-\tfrac1{24}\!\int(18-23Y)}_{-13/48},$$
all over $(0,1)$, using $\int_0^1\frac{\ln(1-Y)}Y=\int_0^1\frac{\ln Y}{1-Y}=-\zeta(2)$ and
$\int_0^1\frac{\ln(1-Y)+Y}{Y^2}=-1$. The sum is $\frac1{16}+\frac13\zeta(2)$, so
$\mathrm L=\frac{11}{48}+\frac13\zeta(2)$. The only transcendental input is
$\mathrm{Li}_2(1)=\zeta(2)$ (`Li₂_one` in `QED/Polylog/`). Mode `exact` of the script
checks each piece to 30 digits.

## 4. The crossed-ladder unit X

### 4.1 Integrand and regulators

X has no UV subdivergence and is IR finite at $q=0$, so it can be taken at $\lambda=0$,
$\Lambda=\infty$ directly (the limit interchange is the obligation of section 8). In the
variables of section 2.2, $D=Y^2+b^2/U$, $U=b+w$, and
$$f_{\rm X}=\frac{P_2(b,w)}{4U^4(Y^2U+b^2)^2}+\frac{P_1(b,w)}{4U^4(Y^2U+b^2)}, \tag{4.1}$$
with $P_2,P_1$ polynomials of total degree 4 and 3 in $(b,w)$ with coefficients in
$\mathbb Q[z_2,z_3]$; they are
generated by the script from the engine (function `crossed_Phi`).

### 4.2 Outer integrations

1. **$w\in(e,\infty)$:** $Y^2U+b^2$ is linear in $w$ and its resultant with $U$ is $b^2$, so
   the $w$-integral is
   $R_0(b)+R_1(b)\,\ln\dfrac{Y^2(b+e)}{(b+Yz_2)(b+Yz_3)}$, using the factorization
   $$Y^2(b+e)+b^2=(b+Yz_2)(b+Yz_3), \tag{4.2}$$
   which holds because $Y^2-4z_2z_3=(z_2-z_3)^2$. Here $R_1=\mathrm{poly}_3(b)/(4b^5)$ and
   $R_0=\mathrm{poly}_6(b)/[4Y\,b^3(b+e)^3(b+Yz_2)(b+Yz_3)]$.
2. **$b\in(g,\infty)$:** partial fractions in $b$ (poles at $0,-e,-Yz_2,-Yz_3$, all outside
   the range) and
   $$\int_0^\infty\Bigl[\frac{\ln(t+C)}{t+D}-\frac{\ln(t+1)}{t+1}\Bigr]dt
   =-\tfrac12\ln^2D-\mathrm{Li}_2\Bigl(1-\frac CD\Bigr)\quad(C,D>0) \tag{4.3}$$
   (the reference term cancels because the simple-pole residues sum to zero).

The result is
$$\boxed{\ \mathrm X=\int_{z_2,z_3>0,\ z_2+z_3<1}\Phi_{\rm X}(z_2,z_3)\,dz_2\,dz_3\ } \tag{4.4}$$
where $\Phi_{\rm X}$ is an explicit combination (about 1600 operations) of rational functions
of $z_2,z_3$, logarithms of $g+d$ for $d\in\{0,e,Yz_2,Yz_3\}$ and of $Y$, and
$\mathrm{Li}_2\bigl(1-\frac{g+C}{g+D}\bigr)$ for $C\in\{e,Yz_2,Yz_3\}$, $D\in\{0,e,Yz_2,Yz_3\}$.
Every $\mathrm{Li}_2$ argument is real and less than 1; in fact all these $\mathrm{Li}_2$ terms have
coefficient zero, because $R_1$ has no $1/b$ term, so $\Phi_{\rm X}$ is rational functions times
single logarithms (section 4.5). $\Phi_{\rm X}$ has removable
singularities on the line $z_2=z_3$ (from $\ln(C/D)/(C-D)$ with $C\to D$) and integrable
logarithmic behaviour at the edges. It suffers severe cancellation in double precision; the
script evaluates it in 24–30 digit arithmetic.

### 4.3 Numerics

In the variables $Y=z_2+z_3$, $\xi=z_2/Y$ (so that the removable line is $\xi=\frac12$, used
as a split point), with tanh-sinh product rules and 30-digit base precision (raised
automatically near the edges):

| tanh-sinh step | (4.4) | minus BMR-I row e) |
| --- | --- | --- |
| $1/8$ | $-0.46764544608689640$ | $6.7\times10^{-12}$ |
| $1/16$ | $-0.46764544609361451$ | $-8.6\times10^{-16}$ |
| $1/32$ | $-0.467645446093613648672$ | $2.9\times10^{-18}$ |

BMR-I: $\frac16-5\zeta(2)\ln2+\frac{13}6\zeta(2)+\frac54\zeta(3)=-0.467645446093613651\ldots$
Agreement to 17 digits. (Section 11.2 of the derivation document had $-0.467632$ from a 4D
quadrature of the same integrand.)

### 4.4 Toward the exact value

The value contains $\zeta(2)\ln2$ and $\zeta(3)$. A route that stays within the
`QED/Polylog/` inventory:

- integrate (4.4) once more analytically, in $z_3$ at fixed $Y=z_2+z_3$ or in $z_b$ at fixed
  $z_2$. The arguments $1-\frac{g+C}{g+D}$ are rational in the inner parameters, so this
  produces $\mathrm{Li}_3$ and $\mathrm{Li}_2\cdot\ln$ terms of rational arguments, leaving a
  1D integral;
- the constants $\ln2$ and $\zeta(3)$ are expected to enter through $\mathrm{Li}_2(\frac12)$,
  $\mathrm{Li}_3(\frac12)$, $\mathrm{Li}_3(-1)$ and $\int_0^1\ln x\ln(1+x)\,dx/x=-\frac34\zeta(3)$,
  all proved (`Li₂_one_half`, `Li₃_one_half`, `Li₃_neg_one`,
  `integral_log_mul_log_one_add_div`). Which combination actually arises has not been
  determined.

This step has **not** been carried out; it is the main remaining analytic task for X.
Lean effort: high (a 2D integral with $\mathrm{Li}_2$, several new definite-integral
identities, each needing a numerical check before it is attempted).

### 4.5 Exact evaluation

**Status (2026-11-18).** The chain below takes (4.4) to BMR's value. Every algebraic step was
carried out in exact rational arithmetic (sympy). Every step is also checked numerically by
mode `crossedexact` of the script, which rebuilds each object from the engine; the checks
are evidence, not proof. The classical integrals used at the end are standard results
(**recalled**, each with a 40-digit check); all of them are now also proved in Lean (4.5.6).
The Lean evaluation of the one-dimensional integral (4.7) is also done (`QED/TwoLoop/UnitXKernel.lean`, items 3–5 of 4.5.6).

#### 4.5.1 The integrand has no dilogarithm

In step 2 of 4.2 the coefficient $R_1=\mathrm{poly}_3(b)/(4b^5)$ has no simple pole: its
partial fractions run over $b^{-5},\dots,b^{-2}$. The dilogarithms of (4.3) come only from
simple poles, so they enter $\Phi_{\rm X}$ with coefficient zero. (The description of
$\Phi_{\rm X}$ in 4.2 lists them because the generic formula produces them; all have
coefficient zero.) Hence $\Phi_{\rm X}$ is a rational function plus rational multiples of
**single** logarithms.

In the variables $Y=z_2+z_3$, $\xi=z_2/Y$ (so $dz_2\,dz_3=Y\,dY\,d\xi$, $z_b=1-Y$) the
arguments of section 2.2 are $g=Y\xi(1-Y)$, $e=Y^2\xi(1-\xi)$ and
$$g+e=Y\xi(1-Y\xi),\qquad g+Yz_2=Y\xi,\qquad g+Yz_3=Y(\xi+Y-2Y\xi),$$
so that
$$\Phi_{\rm X}=R_1+R_Y\ln Y+R_\xi\ln\xi+R_A\ln(1-Y\xi)+R_B\ln(\xi+Y-2Y\xi), \tag{4.5}$$
with $R_\bullet$ rational. The coefficient of $\ln(1-Y)$ cancels. The denominators are

| coefficient | denominator |
| --- | --- |
| $R_1$ | $12\,Y^2\xi^2(1-Y)^2(1-\xi)^2$ |
| $R_Y$ | $12\,Y\xi^3(1-Y)^4$ |
| $R_\xi$ | $12\,Y^3(1-\xi)^4(2\xi-1)$ |
| $R_A$ | $12\,Y^3\xi^3(1-Y)^4(1-\xi)^4$ |
| $R_B$ | $12\,Y^3\xi^3(1-Y)^4(1-\xi)^4(2\xi-1)$ |

(numerators of total degree up to 16, generated by the script). Two features make the next
integration elementary. In $Y$ the only poles are at $Y=0,1$. In $\xi$ the pole at
$\xi=\frac12$ occurs only in $R_\xi$ and $R_B$, with opposite residues; it multiplies
$\ln\xi-\ln(\xi+Y-2Y\xi)$, which vanishes at $\xi=\frac12$, so it is removable (this is the
removable line $z_2=z_3$ of 4.2).

#### 4.5.2 Integration over $\xi$

At fixed $Y\in(0,1)$, decompose each coefficient of $Y\Phi_{\rm X}$ into partial fractions in
$\xi$. Every term is then $t^{n}\ln(\alpha+\beta t)$ with $t=\xi$ or $t=1-\xi$ and $n\in\mathbb Z$
(or $t^n$ without a logarithm), integrated over $(0,1)$. For $n\le-1$ the endpoint $t=0$ is
handled by finite parts: subtract the Taylor polynomial of $\ln(\alpha+\beta t)$ of degree
$-n-1$, integrate the remainder exactly (for $n=-1$ this gives
$-\mathrm{Li}_2(-\beta/\alpha)$), and record the divergent terms ($t^{-j}$, $\ln t$, $\ln^2t$
at the cutoff). The divergent terms of all pieces cancel exactly: seven independent
coefficients, each zero as a rational function of $Y$. The removable term contributes
$$\int_0^1\frac{\ln\xi-\ln(\xi+Y-2Y\xi)}{2\xi-1}\,d\xi
=\tfrac12\Bigl[\frac{\pi^2}4-\mathrm{Li}_2(1-2Y)+\mathrm{Li}_2(2Y-1)\Bigr]$$
(substitute $u=2\xi-1$; the integrand is $\frac12[\ln(1+u)-\ln(1+\kappa u)]/u$ with
$\kappa=1-2Y$).

The result contains $\ln Y$, $\ln(1-Y)$ and $\mathrm{Li}_2$ at the six arguments
$Y,\ \pm(1-2Y),\ -\frac{Y}{1-Y},\ \frac{2Y-1}{Y},\ \frac{1-2Y}{1-Y}$. With
$$D(Y)=\mathrm{Li}_2(1-2Y)-\mathrm{Li}_2(2Y-1),\qquad
D'(Y)=\frac{2\ln\frac{Y}{1-Y}}{1-2Y},\qquad D(0)=\tfrac{\pi^2}4,\ D(1-Y)=-D(Y),$$
the last three reduce by the two-variable identities (valid for $0<Y<1$)
$$\begin{aligned}
\mathrm{Li}_2\Bigl(-\frac{Y}{1-Y}\Bigr)&=-\mathrm{Li}_2(Y)-\tfrac12\ln^2(1-Y),\\
\mathrm{Li}_2\Bigl(\frac{2Y-1}{Y}\Bigr)&=-D(Y)-\mathrm{Li}_2(Y)-\tfrac12\ln^2Y+\tfrac12\zeta(2),\\
\mathrm{Li}_2\Bigl(\frac{1-2Y}{1-Y}\Bigr)&=D(Y)+\mathrm{Li}_2(Y)-\tfrac12\ln^2(1-Y)+\ln Y\ln(1-Y)-\tfrac12\zeta(2).
\end{aligned}\tag{4.6}$$
The first is Landen's identity. The other two follow by differentiation and the value at
$Y=\frac12$ (both sides vanish there, by $\mathrm{Li}_2(\frac12)=\frac12\zeta(2)-\frac12\ln^22$).
All three are checked to 40 digits at three points. Then
$$\boxed{\ \mathrm X=\int_0^1K_{\rm X}(Y)\,dY\ } \tag{4.7}$$
$$K_{\rm X}=k_L\,\mathrm{Li}_2(Y)+k_D\,D(Y)+k_{aa}\ln^2Y+k_{ab}\ln Y\ln(1-Y)+k_a\ln Y
+k_b\ln(1-Y)+k_z\,\zeta(2)+k_1,$$
with, writing $\varrho(Y)=\frac{5}{6(Y-1)}-\frac{3}{4(Y-1)^2}-\frac{8}{3(Y-1)^3}-\frac{1}{(Y-1)^4}$,

| | coefficient (partial fractions) |
| --- | --- |
| $k_L$ | $-\frac52Y-\frac54+2\varrho+\frac5{6Y}-\frac7{12Y^2}$ |
| $k_D$ | $-\frac76Y-\frac{11}{12}+\varrho+\frac5{6Y}-\frac1{12Y^2}$ |
| $k_{aa}$ | $\frac1{12}Y-\frac7{24}+\frac12\varrho$ |
| $k_{ab}$ | $-\frac43Y-\frac13+\frac5{6Y}-\frac7{12Y^2}$ |
| $k_a$ | $-\frac{11}{12}Y-\frac54-\frac1{8(2Y-1)}+\frac{11}{12(Y-1)}-\frac2{3(Y-1)^2}-\frac1{(Y-1)^3}-\frac5{12Y}$ |
| $k_b$ | $\frac{11}{12}Y-\frac{13}{12}+\frac1{8(2Y-1)}-\frac2{3(Y-1)}-\frac1{(Y-1)^2}+\frac7{6Y}-\frac1{24Y^2}$ |
| $k_z$ | $\frac{23}{12}Y+\frac{19}{24}-\frac12\varrho-\frac5{4Y}+\frac1{8Y^2}$ |
| $k_1$ | $-\frac{17}{12}Y+\frac1{24}+\frac2{3(Y-1)}+\frac1{(Y-1)^2}+\frac3{8Y}$ |

There is no $\ln^2(1-Y)$ term and no $\ln 2$. Every $\mathrm{Li}_2$ argument lies in
$[-1,1]$, the domain of the power series used in `QED/Polylog/`. The poles cancel:
$K_{\rm X}$ is smooth on $(0,1)$ (the $(2Y-1)^{-1}$ terms multiply $\ln Y-\ln(1-Y)$),
$K_{\rm X}(Y)=-\frac14\ln^2Y-\frac34\ln Y-\frac74-\frac12\zeta(2)+o(1)$ as $Y\to0$, and
$K_{\rm X}(1)=\frac{\zeta(2)-1}{12}$. At $Y\to1$ the coefficients combine through
$\varrho\,(2\mathrm{Li}_2+D+\frac12\ln^2Y-\frac12\zeta(2))$, a function vanishing at $Y=1$.

**Checks.** $K_{\rm X}$ against a direct $\xi$-quadrature of $Y\Phi_{\rm X}$: difference
$2\times10^{-21}$ at $Y=0.3$ and $4\times10^{-22}$ at $Y=0.7$ (30-digit arithmetic, step
$\frac1{16}$). $\int_0^1K_{\rm X}=-0.46764544609361365159966039867271$, which differs from
BMR-I row e) by $3\times10^{-37}$ at 35-digit precision. This 1D representation therefore
improves the 17-digit check of 4.3.

#### 4.5.3 Reduction to master integrals

Integrate by parts every term of $K_{\rm X}$ whose coefficient has a pole of order $\ge2$ or a
polynomial part, using $\mathrm{Li}_2'(Y)=-\ln(1-Y)/Y$, the formula for $D'$ above and the
derivatives of the logarithms, and repeat on the new terms (each step lowers the weight).
What remains are simple poles. Moving the divergent simple-pole pieces ($Y^{-1}$,
$Y^{-1}\ln Y$, $(Y-1)^{-1}$) into the boundary term gives the exact identity
$$K_{\rm X}=G'+p+K_{\rm m}, \tag{4.8}$$
$$\begin{aligned}
G={}&\Bigl(-\tfrac54Y^2-\tfrac54Y+\tfrac3{2(Y-1)}+\tfrac8{3(Y-1)^2}+\tfrac2{3(Y-1)^3}+\tfrac7{12Y}\Bigr)\mathrm{Li}_2(Y)
+\Bigl(-\tfrac7{12}Y^2-\tfrac{11}{12}Y+\tfrac3{4(Y-1)}+\tfrac4{3(Y-1)^2}+\tfrac1{3(Y-1)^3}+\tfrac1{12Y}\Bigr)D(Y)\\
&+\Bigl(\tfrac1{24}Y^2-\tfrac7{24}Y+\tfrac3{8(Y-1)}+\tfrac2{3(Y-1)^2}+\tfrac1{6(Y-1)^3}-\tfrac18\Bigr)\ln^2Y
+\Bigl(-\tfrac23Y^2-\tfrac13Y+\tfrac7{12Y}\Bigr)\ln Y\ln(1-Y)\\
&+\Bigl(-\tfrac{11}{24}Y^2-\tfrac78Y+\tfrac1{3(Y-1)}+\tfrac1{3(Y-1)^2}+\tfrac5{12}\Bigr)\ln Y
+\Bigl(\tfrac{11}{24}Y^2-\tfrac{19}{24}Y+\tfrac1{3(Y-1)}+\tfrac1{24Y}+\tfrac{23}{24}\Bigr)\ln(1-Y)\\
&-\zeta(2)\Bigl(\tfrac3{8(Y-1)}+\tfrac2{3(Y-1)^2}+\tfrac1{6(Y-1)^3}+\tfrac1{8Y}\Bigr)-\tfrac1{3(Y-1)},
\end{aligned}$$
$$p(Y)=\tfrac1{24}\bigl(30+19\zeta(2)+(46\zeta(2)-34)Y\bigr),$$
$$\begin{aligned}
K_{\rm m}={}&\tfrac56\Bigl[\frac{\mathrm{Li}_2(Y)}Y+\frac{\ln Y\ln(1-Y)}Y+\frac{D(Y)-\frac32\zeta(2)}Y
+2\,\frac{\mathrm{Li}_2(Y)-\zeta(2)}{Y-1}+\frac{D(Y)+\frac32\zeta(2)}{Y-1}\Bigr]\\
&+\tfrac5{12}\frac{\ln^2Y}{Y-1}+\tfrac5{12}\frac{\ln Y}{Y-1}+\tfrac{11}6\frac{\ln(1-Y)}Y
+\tfrac43\,\frac{\ln Y-\ln(1-Y)}{2Y-1}.
\end{aligned}\tag{4.9}$$
Each term of $K_{\rm m}$ is integrable on $(0,1)$, so $G$ has finite one-sided limits. From
the expansions of $\mathrm{Li}_2$, $D$ and the logarithms at the endpoints (the divergent
parts cancel exactly),
$$G(0^+)=\tfrac{17}{24}+\tfrac14\zeta(2),\qquad G(1^-)=\tfrac13+\tfrac1{12}\zeta(2),\qquad
\int_0^1p=\tfrac{13}{24}+\tfrac74\zeta(2). \tag{4.10}$$
The script checks (4.8) as an identity of rational functions in the basis
$\{\mathrm{Li}_2(Y),D,\ln Y,\ln(1-Y),\zeta(2)\}$, the limits (4.10) by series, and $G$
numerically at $Y=10^{-12}$ and $1-10^{-12}$.

#### 4.5.4 The master integrals

All integrals are over $(0,1)$.

| | integral | value | derivation | Lean |
| --- | --- | --- | --- | --- |
| $M_1$ | $\int\frac{\mathrm{Li}_2(Y)}Y$ | $\zeta(3)$ | $\mathrm{Li}_3(1)$ | proved |
| $M_2$ | $\int\frac{\ln Y\ln(1-Y)}Y$ | $\zeta(3)$ | antiderivative $\mathrm{Li}_3(Y)-\ln Y\,\mathrm{Li}_2(Y)$ | proved |
| $M_3$ | $\int\frac{D(Y)-\frac32\zeta(2)}Y$ | $-3\zeta(2)\ln2-\frac74\zeta(3)$ | (4.11) | proved |
| $M_3'$ | $\int\frac{D(Y)+\frac32\zeta(2)}{Y-1}$ | $=M_3$ | $Y\mapsto1-Y$, $D(1-Y)=-D(Y)$ | proved |
| $M_4$ | $\int\frac{\mathrm{Li}_2(Y)-\zeta(2)}{Y-1}$ | $2\zeta(3)$ | $Y\mapsto1-Y$ and Euler reflection: $=M_1+M_2$; also $=-A_1$ | proved |
| $M_5$ | $\int\frac{\ln^2Y}{Y-1}$ | $-2\zeta(3)$ | $=-J_1$ | proved |
| $M_6$ | $\int\frac{\ln Y}{Y-1}$ | $\zeta(2)$ | $\mathrm{Li}_2(1)$ | proved |
| $M_7$ | $\int\frac{\ln(1-Y)}Y$ | $-\zeta(2)$ | $\mathrm{Li}_2(1)$ | proved |
| $M_8$ | $\int\frac{\ln Y-\ln(1-Y)}{2Y-1}$ | $\frac32\zeta(2)$ | $=-\frac12[D]_0^1=\mathrm{Li}_2(1)-\mathrm{Li}_2(-1)$ | proved |

The only master with $\ln2$ is $M_3$. Put $x=1-2Y$; then $dY/Y=-dx/(1-x)$ and
$D=\mathrm{Li}_2(x)-\mathrm{Li}_2(-x)$, so
$M_3=\int_{-1}^1\frac{\mathrm{Li}_2(x)-\mathrm{Li}_2(-x)-\frac32\zeta(2)}{1-x}\,dx$. Folding
$[-1,0]$ onto $[0,1]$,
$$M_3=(A_1-A_2)-A_3+A_4-\tfrac32\zeta(2)\ln2, \tag{4.11}$$
$$\begin{aligned}
A_1&=\int_0^1\frac{\mathrm{Li}_2(x)-\zeta(2)}{1-x}=-J_1=-2\zeta(3), &
A_2&=\int_0^1\frac{\mathrm{Li}_2(-x)+\frac12\zeta(2)}{1-x}=-J_2=\tfrac58\zeta(3),\\
A_3&=\int_0^1\frac{\mathrm{Li}_2(x)}{1+x}=\zeta(2)\ln2+J_2=\zeta(2)\ln2-\tfrac58\zeta(3), &
A_4&=\int_0^1\frac{\mathrm{Li}_2(-x)}{1+x}=-\tfrac12\zeta(2)\ln2+J_3=\tfrac14\zeta(3)-\tfrac12\zeta(2)\ln2,
\end{aligned}$$
each by one integration by parts against $\mp\ln(1\mp x)$ (the boundary terms vanish or give
$\mathrm{Li}_2(\pm1)\ln2$), with the three classical integrals
$$J_1=\int_0^1\frac{\ln^2(1-x)}x=2\zeta(3),\qquad
J_3=\int_0^1\frac{\ln^2(1+x)}x=\tfrac14\zeta(3),\qquad
J_2=\int_0^1\frac{\ln(1-x)\ln(1+x)}x=-\tfrac14J_1-\tfrac12J_3=-\tfrac58\zeta(3).$$
$J_1$ has the antiderivative $\ln x\ln^2(1-x)+2\ln(1-x)\mathrm{Li}_2(1-x)-2\mathrm{Li}_3(1-x)$,
so $J_1=2\mathrm{Li}_3(1)$. $J_3$ has the antiderivative
$\ln x\ln^2(1+x)-\frac23\ln^3(1+x)-2\ln(1+x)\mathrm{Li}_2(\frac1{1+x})-2\mathrm{Li}_3(\frac1{1+x})$,
so $J_3=2\zeta(3)-\frac23\ln^32-2\ln2\,\mathrm{Li}_2(\frac12)-2\mathrm{Li}_3(\frac12)$. This is
where $\ln2$ enters, and it reduces to $\frac14\zeta(3)$ by `Li₂_one_half` and `Li₃_one_half`
(Landen on $[\frac12,1]$, `QED/Polylog/Landen.lean`). $J_2$ follows from
$\ln(1-x)\ln(1+x)=\frac12[\ln^2(1-x^2)-\ln^2(1-x)-\ln^2(1+x)]$ and
$\int_0^1\ln^2(1-x^2)\,dx/x=\frac12J_1$. Every master and every $A_i$, $J_i$ is checked to 40
digits in mode `crossedexact`; the largest deviation is $4\times10^{-35}$ (for $M_8$, limited by
quadrature near its interior split points), all others are below $10^{-39}$.

#### 4.5.5 Assembly

By (4.8)–(4.10) and the table,
$$\begin{aligned}
\mathrm X&=G(1^-)-G(0^+)+\int_0^1p+\tfrac56(M_1+M_2+M_3+2M_4+M_3')+\tfrac5{12}(M_5+M_6)
+\tfrac{11}6M_7+\tfrac43M_8\\
&=\tfrac16+\tfrac{13}6\zeta(2)+\tfrac{25}6\zeta(3)+\tfrac53M_3
=\tfrac16-5\zeta(2)\ln2+\tfrac{13}6\zeta(2)+\tfrac54\zeta(3),
\end{aligned}\tag{4.12}$$
which is BMR-I row e). The sum is evaluated symbolically by the script, and its numerical
value agrees with BMR to $6\times10^{-42}$. So the exact value of X is **derived** from the
representation (4.4), not just matched numerically. The derivation rests on the symbolic
steps above (exact, machine-checked in rational arithmetic, not proved in Lean) and on the
recalled classical values in 4.5.4.

| step | object | check |
| --- | --- | --- |
| 4.5.1 | (4.5): no $\mathrm{Li}_2$; letters | symbolic |
| 4.5.2 | endpoint divergences of the $\xi$-integral | 7 coefficients, exactly zero |
| 4.5.2 | (4.6) | 40 digits, 3 points |
| 4.5.2 | $K_{\rm X}$ vs $\xi$-quadrature of (4.4) | $2\times10^{-21}$ |
| 4.5.2 | $\int_0^1K_{\rm X}$ vs BMR | $3\times10^{-37}$ |
| 4.5.3 | (4.8) | exact identity |
| 4.5.3 | (4.10) | exact series; divergent parts zero |
| 4.5.4 | $M_1,\dots,M_8$, $A_1,\dots,A_4$, $J_1,J_2,J_3$ | 40 digits |
| 4.5.5 | (4.12) | symbolic; $6\times10^{-42}$ numerically |

#### 4.5.6 What is proved in Lean

Proved, with integrability and only the standard axioms (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`):

- `QED/Polylog/ExtraIntegrals.lean` (namespace `QED.Polylog`). The classical inputs:
  $\int_0^1\mathrm{Li}_2(x)/x=\zeta(3)$ (`intervalIntegrable_and_integral_Li₂_div`),
  $\int_0^1\ln x\ln(1-x)/x=\zeta(3)$, $J_1$ (`…_log_one_sub_sq_div`),
  $\int_0^1\ln^2(1-x^2)/x=\zeta(3)$, $J_3$ (`…_log_one_add_sq_div`, through `Li₂_one_half` and
  `Li₃_one_half`), $J_2$ (`…_log_one_sub_mul_log_one_add_div`),
  $\int_0^1\ln(1-x)/x=-\zeta(2)$ and $A_1,\dots,A_4$ (`intervalIntegrable_and_integral_A₁` …
  `_A₄`), all with explicit antiderivatives (`logOneSubSqPrim`, `logOneAddSqPrim`,
  `logOneSubMulLogOneAddPrim`, `primA₁` … `primA₄`) and their one-sided limits. Also proved:
  monotonicity of $\mathrm{Li}_2$ on $[-1,1]$ (`monotoneOn_Li₂`), hence
  $-\frac{\pi^2}{12}\le\mathrm{Li}_2\le\frac{\pi^2}6$ there.
- `QED/TwoLoop/UnitX.lean` (namespace `QED.TwoLoop.Units`). All eight masters of 4.5.4,
  $M_1,\dots,M_8$ and $M_3'$, as `IntervalIntegrable … ∧ ∫ … = value`. For example $M_3$ is
  `intervalIntegrable_and_integral_crossedD_sub_div`, with $D$ = `crossedD`; it is proved
  directly on $[0,\frac12]$ and $[\frac12,1]$ with the antiderivatives
  $-(H_1-H_2)(1-2Y)$ and $(H_4-H_3)(2Y-1)-\frac{\pi^2}4\ln(2Y)$ ($H_i$ = `primAᵢ`). Also
  proved: the arithmetic of (4.12) (`crossedUnit_assembly`). With the boundary constants of
  (4.10) inserted as numbers, the combination of the eight master integrals equals
  $\frac16-5\zeta(2)\ln2+\frac{13}6\zeta(2)+\frac54\zeta(3)$.

**Not proved (the remaining gap for X).**

1. The representation (4.4) and its link to the model (section 8, items 1–11).
2. The step from (4.4) to (4.7): the $\xi$-integration with its finite parts, and the
   identities (4.6) (their left-hand arguments leave $[-1,1]$ on part of $(0,1)$, where the
   Lean power-series $\mathrm{Li}_2$ is not the dilogarithm; (4.7) itself uses only arguments
   in $[-1,1]$).
3. The identity (4.8) $K_{\rm X}=G'+p+K_{\rm m}$ on $(0,1)\setminus\{\frac12\}$: a
   derivative computation with atoms $\mathrm{Li}_2(Y)$, $\mathrm{Li}_2(\pm(1-2Y))$, $\ln Y$,
   $\ln(1-Y)$, mechanical but large.
4. The one-sided limits (4.10) of $G$. At $Y\to0$ they need
   $D(Y)=\frac{\pi^2}4+2Y\ln Y-2Y+o(Y)$ and $\mathrm{Li}_2(Y)=Y+o(Y)$. At $Y\to1$ the
   coefficients of $G$ have poles of order 3, and the limit needs the expansion of
   $2\mathrm{Li}_2(Y)+D(Y)+\frac12\ln^2Y-\frac12\zeta(2)$ to order $(1-Y)^3$, with its
   logarithmic terms.
5. The integrability of $K_{\rm X}$ on $(0,1)$. Given 3, it is equivalent to the
   integrability of $G'$; it follows, for example, from a constant sign of $G'$ near each
   endpoint, which needs the same expansions as 4.

Once 3–5 are proved, $\int_0^1K_{\rm X}=G(1^-)-G(0^+)+\int_0^1p+\int_0^1K_{\rm m}$ follows by the
fundamental theorem of calculus on $[0,\frac12]$ and $[\frac12,1]$, and the value follows by
`crossedUnit_assembly`.

## 5. The self-energy unit S

### 5.1 Integrand

For $S_+$ (inner self-energy subgraph $z_3=Y$, $z_b=1-Y$; outer group of three merged lines),
in the variables $(b,x)$ of section 2.2, including the Jacobian,
$$A_2=\frac{x^2(x-1)(b-c)^2(Yx-Y-x+3)}{4b},\qquad
A_1=-\frac{x(x-1)(b-c)^2(2Yx+Y-2x+2)}{2b^2},\qquad c=Y(1-Y), \tag{5.1}$$
with $D=M_{\rm in}+bh(x)$ and $b\ge c$. $S_-=S_+$ by the mirror symmetry (section 11.2 of the
derivation document; here used, not proved).

### 5.2 Counterterms in the inner parameter

From `sigma_onshell` of `two_loop_units.py` (Feynman parameter $Y$ on the electron line,
$M_\mu=Y^2+(1-Y)\mu$, $\ell=\ln(M_\Lambda/M_\lambda)$):
$$d_2(Y)=-\tfrac{1-Y}2\,\ell-(1+Y)Y(1-Y)\Bigl(\frac1{M_\Lambda}-\frac1{M_\lambda}\Bigr),\qquad
\sigma(Y)=\tfrac{1+Y}2\,\ell,\qquad d_m=d_2-\sigma ,$$
and the two counterterm graphs on the internal line of the one-loop vertex (the script's
`S_side_bare_plus_ct`), per unit $d_2$ and $d_m$:
$$V_k(\lambda)=\int_0^1\frac{x^2(x-1)\bigl(3x^3+3x^2+\lambda^2(2+2x-4x^2)\bigr)}{2(x^2+(1-x)\lambda^2)^2}dx
\to-1,\qquad
V_m(\lambda)=\int_0^1\frac{x^2(1-x)\bigl(2x^2+3\lambda^2(1-x)\bigr)}{2(x^2+(1-x)\lambda^2)^2}dx\to\tfrac12 .$$
The side unit is $S_+ +d_2V_k+d_mV_m$ (with $\delta_{2,m}=r\,d_{2,m}$).

### 5.3 Exact representation at finite $\lambda$, $\Lambda=\infty$

$$\mathrm S(\lambda)=2\int_0^1dY\Bigl\{\int_0^1dx\,\bigl[E_{\rm S}(Y,x)-e_0(x)\bigr]
+\bar d_2(Y)V_k(\lambda)+\bar d_m(Y)V_m(\lambda)\Bigr\}, \tag{5.3}$$
where $E_{\rm S}$ is the $b$-integral of (5.1) over $(c,\infty)$ at $M=M_\lambda$, and the bars
denote the finite parts ($\ell\to-\ln M_\lambda$, $1/M_\Lambda\to0$):
$\bar d_2=\frac{1-Y}2\ln M+\frac{(1+Y)Y(1-Y)}M$, $\bar\sigma=-\frac{1+Y}2\ln M$.
At $\lambda=0.01$: $\mathrm S=-4.5793668$, against $-4.579348$ at $\Lambda=1000$ in section
11.3, whose $\Lambda$-remainder for S is about $-1.2\times10^{-5}$ at this $\lambda$. At
finite $(\lambda,\Lambda)=(0.5,3)$ the same construction with all four Pauli–Villars terms
gives $-0.1787924$ per side, against $-0.1787912$ from the script's insertion form.

### 5.4 The limit: where the logarithm sits

At $\lambda=0$ the two-loop part $G_{\rm S}(Y,x)=E_{\rm S}-e_0$ is finite as $x\to0$ and behaves
like $-\frac14\ln Y$ as $Y\to0$: it is IR finite and integrable. The whole IR logarithm of S
comes from $\bar d_2$, through $\int_0^1\frac{(1+Y)Y(1-Y)}{Y^2+(1-Y)\lambda^2}dY=-\ln\lambda-\frac12
+o(1)$:
$$\int_0^1\bar d_2=-\ln\lambda-\tfrac54,\qquad \int_0^1\bar d_m=-\ln\lambda-\tfrac52,\qquad
2\Bigl[(-\ln\lambda-\tfrac54)(-1)+(-\ln\lambda-\tfrac52)\tfrac12\Bigr]=\ln\lambda .$$
Hence
$$\boxed{\ \mathrm S=\ln\lambda+b_{\rm S}+o(1),\qquad b_{\rm S}=2\int_0^1K_{\rm S}(Y)\,dY\ } \tag{5.5}$$
$$K_{\rm S}(Y)=\int_0^1G_{\rm S}(Y,x)\,dx=\frac{(1-Y)(3Y^2+2Y+1)\ln(1-Y)}{12Y^2}
+\frac{3Y^2-3Y+2}{24Y}+\frac{Y(9Y-8)\ln Y}{12(1-Y)} .$$
**Numerics:** $b_{\rm S}=-0.08997802228274214549080505554867506307$, equal to BMR-I row b),
$\frac{11}{24}-\frac13\zeta(2)$, in all 40 digits. The coefficient of $\ln\lambda$ is
BMR's $+1$.

### 5.5 Exact evaluation (by hand, checked)

With $t=1-Y$: $\int_0^1K_{\rm S}=\frac1{12}\int(1-3Y)\ln(1-Y)\,[=\tfrac5{48}]
+\frac1{12}\int\frac{\ln(1-Y)}Y\,[=-\tfrac{\zeta(2)}{12}]
+\frac1{12}\int\bigl[\frac{\ln(1-Y)}{Y^2}+\frac1Y\bigr]\,[=-\tfrac1{12}]
+\int(\frac Y8-\frac18)\,[=-\tfrac1{16}]
+\frac1{12}\int\frac{\ln Y}{t}\,[=-\tfrac{\zeta(2)}{12}]
+\frac1{12}\int(-1-9Y)\ln Y\,[=\tfrac{13}{48}]
=\frac{11}{48}-\frac{\zeta(2)}6$, so $b_{\rm S}=\frac{11}{24}-\frac13\zeta(2)$.
Only $\mathrm{Li}_2(1)$ is needed.

## 6. The corner unit C

### 6.1 Integrand

For $C_+$ in the variables of section 2.2 ($Y=y_3+y_4$, $y_b=1-Y$, $g=y_3y_b$, $e=y_3y_4$),
including the Jacobian,
$$A_2=\frac{x(b-g)\bigl[p_1(x)\,b+x(2-x)(1-2y_3)\,g\bigr]}{4b^2},\qquad
A_1=-\frac{x(b-g)\bigl[2(x-1)b^2+p_2(x)\,b-3x(1-2y_3)\,g\bigr]}{4b^3}, \tag{6.2}$$
$$p_1=2x^3y_3^2-2x^3y_3-6x^2y_3^2-4x^2y_3y_4+6x^2y_3+2x^2y_4-x^2+6xy_3^2+8xy_3y_4-6xy_3+2xy_4^2-6xy_4-2y_3^2-4y_3y_4+4y_3-2y_4^2+4y_4,$$
$$p_2=8x^2y_3^2-8x^2y_3-10xy_3^2-4xy_3y_4+2xy_3-2xy_4+5x+2y_3^2+4y_3-2y_4^2+4y_4-4,$$
with $D=M_{\rm in}-\lambda^2e+bh(x)$ and $b\ge\beta(x)=\max(g,ex/(1-x))$. $C_-=C_+$ by the
mirror symmetry (used, not proved).

### 6.2 Counterterm

$\delta_1$ is spread over the inner simplex with density
$-\bigl[\frac{Y^2+2Y-2}{2M}-\frac12\ln\frac{M}{M_\Lambda}\bigr]$ per unit area (the merged
one-loop density of 3.2 divided by $Y$), $M=Y^2+(1-Y)\lambda^2$.

### 6.3 Exact representation at finite $\lambda$, $\Lambda=\infty$

$$\mathrm C(\lambda)=2\int_{\Delta_2}dy_3\,dy_4\Bigl\{\int_0^1dx\,\bigl[E_{\rm C}-e_0\bigr]
-F_2^{(2)}(\lambda)\Bigl[\frac{Y^2+2Y-2}{2M}-\frac12\ln M\Bigr]\Bigr\} \tag{6.3}$$
($E_{\rm C}$ the $b$-integral of (6.2), two branches in $x$). At $\lambda=0.01$ a 3D Gauss
rule gives $3.92671$, against $3.926720$ at $\Lambda=1000$ in section 11.3.

### 6.4 The limit

At $\lambda=0$ the two-loop part $G_{\rm C}=E_{\rm C}-e_0$ (at $M=Y^2$, $h=x$) is finite as
$x\to0$ — the outer-soft region gives no logarithm for the corner, unlike the ladder — and
grows like $1/Y$ as $Y\to0$, which is integrable against the area element $Y\,dY$. The
whole IR logarithm then comes from the counterterm:
$\int_{\Delta_2}\frac{Y^2+2Y-2}{2M}=\ln\lambda+\frac54+o(1)$ and
$\int_{\Delta_2}\frac12\ln M\to-\frac14$, so
$$\boxed{\ \mathrm C=-\ln\lambda+b_{\rm C}+o(1),\qquad
b_{\rm C}=2\int_{\Delta_2}dy_3\,dy_4\int_0^1dx\,G_{\rm C}(y_3,y_4,x)-\frac32\ } \tag{6.5}$$
**Numerics.** The 3D integral is evaluated with a fixed tanh-sinh rule in $x$ (step
$\frac1{16}$, on $[0,x_*]$ and $[x_*,1]$) and a tanh-sinh product rule in
$(Y,\,y_3/Y)$, split at $y_3=y_4$, in 24-digit base precision:

| outer step | $b_{\rm C}$ from (6.5) | minus BMR-I row c) finite part |
| --- | --- | --- |
| $1/4$ | $-0.5640209700985589$ | $-2.9\times10^{-8}$ |
| $1/8$ | $-0.5640209413584455$ | $-1.4\times10^{-11}$ |

BMR-I row c): $-\frac{67}{24}+2\zeta(2)\ln2+\frac13\zeta(2)-\frac12\zeta(3)-\ln\lambda$, with
finite part $-0.56402094134468281559\ldots$ The coefficient of $\ln\lambda$ is BMR's $-1$.

### 6.5 Toward the exact value

(Superseded by 6.6.1: the $x$-integral in fact produces no $\mathrm{Li}_2$.) The $x$-integral of $G_{\rm C}$ is elementary up to $\mathrm{Li}_2$: on $x<x_*$ the logarithms
are $\ln x$ and $\ln(Y^2+gx)$; on $x>x_*$ they are $\ln x$, $\ln(1-x)$ and, by the
factorization
$$Y^2(1-x)+y_3y_4x^2=y_3y_4\Bigl(\frac Y{y_3}-x\Bigr)\Bigl(\frac Y{y_4}-x\Bigr), \tag{6.6}$$
$\ln(Y/y_3-x)$ and $\ln(Y/y_4-x)$. The denominators are powers of $x$, $1-x$ and the same
linear factors. So $b_{\rm C}$ is a 2D integral of rational functions, logarithms and
$\mathrm{Li}_2$ of rational arguments, of the same type as (4.4) for X; the same comments
on the exact evaluation apply. Not carried out.

### 6.6 Exact evaluation

**Status (2026-11-18).** The chain below takes (6.5) to BMR's value of $b_{\rm C}$, and hence of
S$+$C. Every algebraic step was carried out in exact rational arithmetic (sympy). Every step is
also checked numerically by mode `cornerexact` of the script, which rebuilds each object from the
engine; the checks are evidence, not proof. No new master integral is needed: the reduction ends
on the masters of X (4.5.4), all proved in Lean. The one-dimensional integral (6.10) itself, with
its value, is **proved in Lean** (6.6.5). The steps before it, (6.5) $\to$ (6.8) $\to$ (6.10),
are not.


**Update (2026-11-18).** Items 3–5 are now proved: the integration-by-parts identity (4.8)
(`hasDerivAt_crossedBoundary`), the endpoint limits of $G$ (`tendsto_crossedBoundary_zero`, `…_one`,
via fifth-order bounds for $\mathrm{Li}_2$ near 0 and for $D(s)+\ln s\ln(1-2s)$, in
`QED/Polylog/ExtraIntegralsX.lean`, `QED/TwoLoop/UnitXKernelBasic.lean`), and the integrability and
value of $\int_0^1K_{\rm X}$ (`QED/TwoLoop/UnitXKernel.lean`, `crossedUnit_value`). Items 1–2 remain.
#### 6.6.1 Integration over $x$: no dilogarithm

Use $Y=y_3+y_4$ and $\xi=y_3/Y$, so that $dy_3\,dy_4=Y\,dY\,d\xi$, $g=Y\xi(1-Y)$,
$e=Y^2\xi(1-\xi)$ and $x_*=g/(g+e)=\frac{1-Y}{1-Y\xi}$. At $\lambda=0$, $G_{\rm C}$ is the
$b$-integral of (6.2) at $M=Y^2$, $h=x$, and its logarithms are those of the two arguments
$Y^2+\beta x$ and $\beta x$. On the two branches of section 2.2:

| branch | $\beta$ | $Y^2+\beta x$ | letters of $G_{\rm C}$ |
| --- | --- | --- | --- |
| $x<x_*$ | $g$ | $Y\,(Y+\xi(1-Y)x)$ | $Y,\ \xi,\ 1-Y,\ x,\ Y+\xi(1-Y)x$ |
| $x>x_*$ | $ex/(1-x)$ | $Y^2(1-\xi x)(1-(1-\xi)x)/(1-x)$, by (6.6) | $Y,\ \xi,\ 1-\xi,\ x,\ 1-x,\ 1-\xi x,\ 1-(1-\xi)x$ |

The structural fact that makes the $x$-integral elementary: **every logarithm coefficient is a
polynomial in $x$** (of degree at most 4), and the rational part is a polynomial in $x$ for
$x<x_*$ and has only simple poles at $x=1/\xi$ and $x=1/(1-\xi)$ (that is, $Y/y_3$ and
$Y/y_4$, outside $[0,1]$) for $x>x_*$. For a polynomial $c$ and a letter $a+bx$, choose the
antiderivative $\tilde C$ of $c$ that vanishes at $x=-a/b$; then
$\int c\ln(a+bx)\,dx=\tilde C\ln(a+bx)-\int b\tilde C/(a+bx)\,dx$, and the last integrand is a
polynomial. So no dilogarithm arises. (Section 6.5 expected one; there is none.) The endpoint
values of the letters are
$$x_*=\frac{1-Y}{1-Y\xi},\quad 1-x_*=\frac{Y(1-\xi)}{1-Y\xi},\quad
1-\xi x_*=\frac{1-\xi}{1-Y\xi},\quad
Y+\xi(1-Y)x_*=1-(1-\xi)x_*=\frac{\xi+Y-2Y\xi}{1-Y\xi},$$
and $\ln(1-x)$ enters only through $\tilde C$ vanishing at $x=1$. The result is
$$\Phi_{\rm C}(Y,\xi)=\int_0^1G_{\rm C}\,dx
=R_1+R_Y\ln Y+R_\xi\ln\xi+R_A\ln(1-Y\xi)+R_B\ln(\xi+Y-2Y\xi), \tag{6.7}$$
with $R_\bullet$ rational. The coefficients of $\ln(1-Y)$ and $\ln(1-\xi)$ cancel, so
$\Phi_{\rm C}$ has exactly the letters of $\Phi_{\rm X}$ in (4.5). The denominators are

| coefficient | denominator |
| --- | --- |
| $R_1$ | $24\,Y^2\xi^2(1-\xi)^2$ |
| $R_Y$ | $12\,\xi^3(1-Y)^2$ |
| $R_\xi$ | $12\,Y^3(1-\xi)^4(2\xi-1)$ |
| $R_A$ | $12\,Y^3\xi^3(1-Y)^2(1-\xi)^4$ |
| $R_B$ | $12\,Y^3\xi^3(1-Y)^2(1-\xi)^4(2\xi-1)$ |

(numerators of total degree up to 12, generated by the script). As for X, the pole at
$\xi=\frac12$ (the line $y_3=y_4$) occurs only in $R_\xi$ and $R_B$, with residues
$\pm\frac1{2Y^3}$, and multiplies $\ln\xi-\ln(\xi+Y-2Y\xi)$, which vanishes there. Thus
$$b_{\rm C}=2\int_0^1\!dY\int_0^1\!d\xi\;Y\,\Phi_{\rm C}(Y,\xi)-\frac32 . \tag{6.8}$$

#### 6.6.2 Integration over $\xi$

The $\xi$-integration of $Y\Phi_{\rm C}$ is the procedure of 4.5.2, with the same code: partial
fractions in $\xi$, finite parts at $\xi=0,1$ (the seven divergent coefficients cancel exactly),
the removable term integrated as in 4.5.2, and the identities (4.6) to reduce the dilogarithm
arguments. The result is
$$\boxed{\ b_{\rm C}=2\int_0^1K_{\rm C}(Y)\,dY-\frac32\ } \tag{6.9}$$
$$K_{\rm C}=k_L\,\mathrm{Li}_2(Y)+k_D\,D(Y)+k_{aa}\ln^2Y+k_{ab}\ln Y\ln(1-Y)+k_a\ln Y
+k_b\ln(1-Y)+k_z\,\zeta(2)+k_1, \tag{6.10}$$
with $D(Y)=\mathrm{Li}_2(1-2Y)-\mathrm{Li}_2(2Y-1)$ as in 4.5.2 and

| | coefficient (partial fractions) |
| --- | --- |
| $k_L$ | $Y-\frac12-\frac1{3(Y-1)}-\frac1{6Y}+\frac1{2Y^2}$ |
| $k_D$ | $\frac23Y-\frac13-\frac1{6(Y-1)}-\frac1{6Y}$ |
| $k_{aa}$ | $\frac16Y-\frac1{12}-\frac1{12(Y-1)}$ |
| $k_{ab}$ | $\frac13Y-\frac16-\frac1{6Y}+\frac1{2Y^2}$ |
| $k_a$ | $\frac16Y-\frac14-\frac5{12(Y-1)}+\frac1{2Y}$ |
| $k_b$ | $-\frac23Y+\frac43-\frac5{6Y}+\frac1{6Y^2}$ |
| $k_z$ | $-\frac23Y+\frac13+\frac1{12(Y-1)}+\frac1{4Y}$ |
| $k_1$ | $\frac{31}{24}Y-\frac76-\frac1{3Y}$ |

$K_{\rm C}$ is simpler than $K_{\rm X}$: no $(2Y-1)^{-1}$ poles, no $\ln^2(1-Y)$, no $\ln2$, poles
of order at most 2 at $Y=0$ and simple poles at $Y=1$. The poles cancel: the $Y^{-2}$ and $Y^{-1}$
terms combine through $(\mathrm{Li}_2(Y)+\ln(1-Y))/Y^2$, $(\ln(1-Y)+Y)/Y^2$ and
$\ln Y\,(\ln(1-Y)+Y)/Y^2$, and the $(Y-1)^{-1}$ terms through
$-\frac13(\mathrm{Li}_2-\zeta(2))-\frac16(D+\frac32\zeta(2))-\frac1{12}\ln^2Y-\frac5{12}\ln Y$,
which vanishes at $Y=1$. Then $K_{\rm C}(Y)=-\frac14\ln Y-\frac18+o(1)$ as $Y\to0$ and
$K_{\rm C}(1)=\frac12\zeta(2)-\frac58$.

**Checks.** $\Phi_{\rm C}$ against an $x$-quadrature of $G_{\rm C}$ (both branches) at three
points: largest difference $1.5\times10^{-31}$ (40-digit arithmetic; $G_{\rm C}$ loses digits to
cancellation). $K_{\rm C}$ against a $\xi$-quadrature of $Y\Phi_{\rm C}$: $1\times10^{-22}$ at
$Y=0.3$ and $2\times10^{-22}$ at $Y=0.7$ (50-digit arithmetic, tanh-sinh step $\frac1{64}$).
$\int_0^1K_{\rm C}=0.46798952932765859220338117972215771$, and
$2\int_0^1K_{\rm C}-\frac32=-0.56402094134468281559323764055568458$, which differs from BMR-I
row c) by $8\times10^{-43}$ at 40-digit precision. This replaces the 10-digit check of 6.4.

#### 6.6.3 Reduction to master integrals

The integration by parts of 4.5.3, applied to $K_{\rm C}$ (now done by a short algorithm in
exact arithmetic: integrate the polynomial and higher-pole parts of each coefficient, from the
weight-two functions down, and move the divergent simple-pole pieces into the boundary term),
gives the exact identity on $(0,1)\setminus\{\frac12\}$
$$K_{\rm C}=G_{\rm C}'+K^{\rm C}_{\rm m}, \tag{6.11}$$
$$\begin{aligned}
G_{\rm C}={}&\Bigl(\tfrac12Y^2-\tfrac12Y-\tfrac1{2Y}\Bigr)\mathrm{Li}_2(Y)+\tfrac13(Y^2-Y)\,D(Y)
+\tfrac1{12}(Y^2-Y)\ln^2Y+\Bigl(\tfrac16Y^2-\tfrac16Y-\tfrac1{2Y}\Bigr)\ln Y\ln(1-Y)\\
&+\Bigl(\tfrac1{12}Y^2-\tfrac14Y-\tfrac12\Bigr)\ln Y
+\Bigl(-\tfrac13Y^2+\tfrac76Y-\tfrac23-\tfrac1{6Y}\Bigr)\ln(1-Y)
-\tfrac13\zeta(2)(Y^2-Y)+\tfrac{37}{48}Y^2-\tfrac74Y,
\end{aligned}$$
$$\begin{aligned}
K^{\rm C}_{\rm m}={}&-\tfrac16\Bigl[\frac{\mathrm{Li}_2(Y)}Y+\frac{\ln Y\ln(1-Y)}Y
+\frac{D(Y)-\frac32\zeta(2)}Y+2\,\frac{\mathrm{Li}_2(Y)-\zeta(2)}{Y-1}
+\frac{D(Y)+\frac32\zeta(2)}{Y-1}\Bigr]\\
&-\tfrac1{12}\Bigl[\frac{\ln^2Y}{Y-1}-\frac{\ln Y}{Y-1}\Bigr]-\tfrac56\,\frac{\ln(1-Y)}Y
-\tfrac16\,\frac{\ln Y-\ln(1-Y)}{2Y-1}.
\end{aligned}$$
There is no polynomial remainder (the $p$ of (4.8) is absorbed into $G_{\rm C}$). The bracket of
$K^{\rm C}_{\rm m}$ is the bracket $M_1+M_2+M_3+2M_4+M_3'$ of (4.9). $G_{\rm C}$ has only a simple
pole at $Y=0$, and its one-sided limits are
$$G_{\rm C}(0^+)=-\tfrac13,\qquad G_{\rm C}(1^-)=-\tfrac{47}{48}-\tfrac12\zeta(2). \tag{6.12}$$
At $Y\to0$ they use $\mathrm{Li}_2(Y)/Y\to1$, $\ln(1-Y)/Y\to-1$ and
$\ln Y\,(\ln(1-Y)+Y)/Y\to0$; at $Y\to1$ the coefficient of $\ln(1-Y)$ vanishes at $Y=1$.

#### 6.6.4 Assembly

By (6.11), (6.12) and the table of 4.5.4,
$$\begin{aligned}
\int_0^1K_{\rm C}&=G_{\rm C}(1^-)-G_{\rm C}(0^+)-\tfrac16(M_1+M_2+M_3+2M_4+M_3')
-\tfrac1{12}(M_5-M_6)-\tfrac56M_7-\tfrac16M_8\\
&=-\tfrac{31}{48}+\tfrac16\zeta(2)-\tfrac56\zeta(3)-\tfrac13M_3
=-\tfrac{31}{48}+\tfrac16\zeta(2)+\zeta(2)\ln2-\tfrac14\zeta(3),
\end{aligned}\tag{6.13}$$
so that
$$b_{\rm C}=-\tfrac{67}{24}+2\zeta(2)\ln2+\tfrac13\zeta(2)-\tfrac12\zeta(3),\qquad
\mathrm S+\mathrm C=b_{\rm S}+b_{\rm C}=-\tfrac73+2\zeta(2)\ln2-\tfrac12\zeta(3),$$
which are BMR-I rows c) (finite part) and the S$+$C value of section 7, with
$b_{\rm S}=\frac{11}{24}-\frac13\zeta(2)$ from 5.5. As for X, $\ln2$ enters only through
$M_3$. The sum is evaluated symbolically by the script; numerically $b_{\rm C}$ and S$+$C agree
with BMR to $8\times10^{-43}$ and $5\times10^{-42}$. So the exact value of C is **derived** from
(6.5).

| step | object | check |
| --- | --- | --- |
| 6.6.1 | log coefficients of $G_{\rm C}$ polynomial in $x$; rational part as stated | symbolic |
| 6.6.1 | (6.7) vs $x$-quadrature of $G_{\rm C}$ | $1.5\times10^{-31}$, 3 points |
| 6.6.2 | endpoint divergences of the $\xi$-integral | 7 coefficients, exactly zero |
| 6.6.2 | (6.10) vs $\xi$-quadrature of $Y\Phi_{\rm C}$ | $2\times10^{-22}$ |
| 6.6.2 | $2\int_0^1K_{\rm C}-\frac32$ vs BMR | $8\times10^{-43}$ |
| 6.6.3 | (6.11) | exact identity |
| 6.6.3 | (6.12) | exact series; divergent parts zero |
| 6.6.4 | masters $M_1,\dots,M_8$ (4.5.4) | 40 digits ($4\times10^{-35}$ for $M_8$) |
| 6.6.4 | (6.13), $b_{\rm C}$, S$+$C | symbolic; $8\times10^{-43}$, $5\times10^{-42}$ |

Reproduce: `nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py cornerexact`
(single process, about 20 s, under 0.1 GB).

#### 6.6.5 What is proved in Lean

Proved, with integrability and only the standard axioms (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`):

- `QED/Polylog/ExtraIntegralsC.lean` (namespace `QED.Polylog`): $\mathrm{Li}_2(x)\le-\ln(1-x)$ on
  $[0,1)$ (`Li₂_le_neg_log_one_sub`, by comparing the series), $|\ln(1-x)+x|\le x^2/(1-x)$
  (`abs_log_one_sub_add_le`), $\mathrm{Li}_2(x)/x\to1$ (`tendsto_Li₂_div_zero`),
  $\int_0^1(\mathrm{Li}_2(x)+\ln(1-x))/x^2=1-\zeta(2)$ (antiderivative $-\mathrm{Li}_2(x)/x$),
  $\int_0^1(\ln(1-x)+x)/x^2=-1$, the integrability of $\ln x\,(\ln(1-x)+x)/x^2$ (dominated by
  $\ln x/(x-1)$), and $\ln x\,(\ln(1-x)+x)/x\to0$ as $x\to0^+$.
- `QED/TwoLoop/UnitC.lean` (namespace `QED.TwoLoop.Units`), with $K_{\rm C}$ = `cornerKernel`
  (the table of (6.10), $\zeta(2)=\pi^2/6$, $D$ = `crossedD`), $G_{\rm C}$ = `cornerBoundary`,
  $K^{\rm C}_{\rm m}$ = `cornerMasterKernel`:
  - `intervalIntegrable_cornerKernel`, from a decomposition of $K_{\rm C}$ on $(0,1)$ into
    polynomials times integrable functions (`cornerKernel_eq_decomp`);
  - `hasDerivAt_cornerBoundary`: (6.11) on $(0,1)\setminus\{\frac12\}$;
  - `tendsto_cornerBoundary_zero`, `tendsto_cornerBoundary_one`: (6.12);
  - `intervalIntegrable_and_integral_cornerKernel`:
    $\int_0^1K_{\rm C}=-\frac{31}{48}+\frac{\pi^2}{36}+\frac{\pi^2}6\ln2-\frac{\zeta(3)}4$
    (the fundamental theorem of calculus on $[0,\frac12]$ and $[\frac12,1]$, plus the masters);
  - `cornerUnit_finitePart_value`: $2\int_0^1K_{\rm C}-\frac32
    =-\frac{67}{24}+2\zeta(2)\ln2+\frac13\zeta(2)-\frac12\zeta(3)$;
  - `selfEnergyCornerUnit_value`: $2\int_0^1K_{\rm S}+(2\int_0^1K_{\rm C}-\frac32)
    =-\frac73+2\zeta(2)\ln2-\frac12\zeta(3)$, with $K_{\rm S}$ = `selfEnergyKernel` of
    `QED/TwoLoop/UnitLS.lean`;
  - `cornerUnit_assembly`: the arithmetic of (6.13) from the master integrals, in the form of
    `crossedUnit_assembly`.

So for C, unlike X, the one-dimensional integral is proved in full: the analogues of items 3–5
of the list in 4.5.6 are proved here.

**Not proved (the remaining gap for C and S$+$C).**

1. The representations (6.5) and (5.5), and their link to the model (section 8, items 1–11),
   including the regulator limits and the counterterm constant $-\frac32$.
2. The step (6.5) $\to$ (6.8): the $x$-integration of 6.6.1 (polynomial antiderivatives with
   the two branches; the structural facts about $G_{\rm C}$ are checked symbolically, not proved).
3. The step (6.8) $\to$ (6.10): the $\xi$-integration with its finite parts and the identities
   (4.6), exactly as item 2 of 4.5.6 for X (part of the left-hand dilogarithm arguments of (4.6)
   leaves $[-1,1]$, where the Lean power series $\mathrm{Li}_2$ is not the dilogarithm).

## 7. S $+$ C: the infrared-finite grouping

Adding (5.5) and (6.5), the logarithms cancel:
$$\boxed{\ \mathrm S+\mathrm C=2\int_0^1K_{\rm S}\,dY+2\int_{\Delta_2}\!\int_0^1G_{\rm C}
-\frac32\ } \tag{7.1}$$
The mechanism is visible at finite regulators, before any limit. With the Ward identity
$\delta_1=\delta_2$ (O2-15) the counterterms of S and C are
$2\delta_2\bigl[V_k+V_m+F_2^{(2)}\bigr]-2\sigma V_m$ (in units of $r$), and
$V_k+V_m+F_2^{(2)}\to-1+\frac12+\frac12=0$ as $\lambda\to0$. The
infrared-divergent constant $\delta_2$ therefore multiplies a vanishing factor, and
$\sigma$ is infrared finite; together with the IR finiteness of the two-loop parts (5.4,
6.4), this is why S$+$C has no logarithm. In (7.1) the constant $-\frac32$ collects the
finite parts of the counterterms after the $\ln M_\Lambda$ terms have been cancelled against
the two-loop parts at each inner point (sections 5.3 and 6.3; the finite parts of
$\delta_1$ and $\delta_2$ separately are allocation-dependent and differ by $\frac14$). So the
grouping S$+$C is IR finite in this representation, as section 11.6 item 1 of the
derivation document recommends, and no logarithm has to be split off numerically.

**Numerics.** With $b_{\rm S}$ from (5.5) (exact to 40 digits) the agreement of S$+$C with
BMR's $-\frac73+2\zeta(2)\ln2-\frac12\zeta(3)=-0.65399896362742495\ldots$ is that of $b_{\rm C}$
in the table of 6.4. Against the route-A finite-regulator values of section 11.4
($-0.653991$ at $\Lambda=1000$, $\lambda=10^{-4}$; fitted limit $-0.654020\pm8\times10^{-5}$) the
difference is within the quoted uncertainties there.

## 8. What connects these representations to the model

The representations start from the regulated parametric integrand of each unit, the
object section 11 of the derivation document evaluates. The chain from the frozen model to
that integrand, and from the integrand to the boxed formulas, uses the following steps;
none is proved yet.

From the model to the parametric integrand (as listed in the derivation document):

1. **O2-2, O2-7:** the order-5 1PI vertex is the sum of the classes; the energy-first joint
   prescription has a unique $\varepsilon\to0^+$ limit for each class.
2. **O2-10, O2-20:** Feynman parametrization inside the energy integral; the energy and
   spatial integrals give the covariant parametric form (the step from the energy-first value
   to the formula of 2.1). O2-12 (positivity of $V$) for dominated convergence.
3. **O2-11, O2-21, O2-22:** the numerator algebra and the projector $P_2$; the existence of
   form factors per unit (mirror-closed units); the limit $q^2\to0^+$ at fixed regulators,
   which is what makes $f_G$ the $q\to0$ Pauli coefficient.
4. **O2-13, O2-15, O2-27:** the counterterm insertion identities, $\delta_1=\delta_2$, and the
   order separation, which identify the counterterm terms with $\delta_1F_2^{(2)}$,
   $d_2V_k+d_mV_m$, etc.
5. **Mirror symmetry** $C_-=C_+$, $S_-=S_+$ as an identity of parametric integrals (a
   relabelling; part of O2-21).

From the parametric integrand to the formulas of this document:

6. **Cheng–Wu** for these integrands (Fubini–Tonelli plus a scaling change of variables;
   the integrands are integrable at fixed regulators by O2-12), and the substitutions of 2.2.
7. **The splitting identity (2.1)** for each graph: polynomial identities, checked
   symbolically; in Lean, `ring` after clearing denominators.
8. **The $b$-integral:** elementary antiderivatives (the masters $I_{j,n}$), with improper
   integrals at $b\to\infty$.
9. **$\Lambda\to\infty$ (part of O2-17):** the inner Pauli–Villars term has the asymptotics
   of 2.3 uniformly in $x$ (the outer integrand is then dominated); the outer Pauli–Villars
   terms tend to zero; the counterterm integrand is placed at the same inner parameter. Each
   step is an interchange of $\lim_\Lambda$ with $\int dx\,dY$ (dominated convergence).
10. **$\lambda\to0$ (O2-23):** for L, subtraction of $T_1$ and dominated convergence for
    $R(\lambda)\to R_0$ near the corner $(Y,x)\to(0,0)$, where both soft regions overlap; for
    S and C, dominated convergence of the two-loop parts near $Y\to0$ (integrands of size
    $\ln Y$, $1/Y$ against $Y\,dY$), plus the explicit counterterm asymptotics. The numerics
    show that no scaling region $Y\sim\lambda$ contributes, which a proof must confirm with a
    uniform bound.
11. **Order of limits.** The derivation takes $\Lambda\to\infty$ at fixed $\lambda$ and then
    $\lambda\to0$. Packet T3 freezes the joint limit $(m_\gamma,\Lambda)\to(0,\infty)$. For L, X
    and S$+$C the joint limit follows from the iterated one if the $\Lambda$-remainder
    (observed $O(\Lambda^{-2})$, $m_\gamma$-independent for L and X, section 11.3 of the
    derivation document) is bounded uniformly in $\lambda$. For S and C separately this fails
    (the $\pm0.67\,\Lambda^{-2}\ln m_\gamma$ term), which is why only S$+$C is stated.

## 9. Lean effort, relative to what exists

| Item | Ingredients | Estimate |
| --- | --- | --- |
| L: value of (3.6) | elementary integrals with endpoint cancellations; `Li₂_one`; improper integrals as in `integral_vpX` | low–moderate (comparable to the VP unit value, `VacuumPolarizationUnit.lean`) |
| S: value of (5.5) | same as L | low–moderate |
| L, S: reduction steps 6–10 | Cheng–Wu, polynomial identities, masters, two limit interchanges each | moderate–high (the limit interchanges dominate) |
| X: value of (4.4) | the reduction of 4.5: the ξ-integration and identities (4.6) (with $\mathrm{Li}_2$ arguments outside $[-1,1]$), the identity $K_{\rm X}=G'+p+K_m$, the endpoint limits of $G$ (third-order poles at 1); the eight master integrals are proved (`QED/Polylog/ExtraIntegrals.lean`, `QED/TwoLoop/UnitX.lean`) | high, mainly the endpoint expansions |
| C: value of $b_{\rm C}$ | the $x$-integration (6.6.1, elementary) and the $\xi$-integration (6.6.2, as for X, with the identities (4.6)); the 1D integral (6.9) and its value are proved (`QED/TwoLoop/UnitC.lean`), with no new master | moderate–high, mainly the $\xi$-integration |
| S$+$C | sum of the two, with the Ward-identity cancellation of 7 | as for C |

## 10. Sources and evidence

- Targets: BMR-I p. 852 (rendered page; rows b)–e)), totals p. 853.
- Parametric functions: CK-R (24)–(37), AKN (55)–(57), (64)–(65); the integrand itself is the
  one validated in section 11 of the derivation document.
- Cheng–Wu theorem, the masters $I_{j,n}$, the dilogarithm formula (4.3) and the special
  values $\mathrm{Li}_2(1)$: standard (**recalled**; the last is proved in `QED/Polylog/`).
- Everything else above is **derived** here and checked by
  `scripts/numerics/two_loop_unit_integrals.py`; the Lean results are listed in section 1.

Reproduce (single process each, niced): `exact` (seconds), `ladder` (under a minute),
`selfenergy` (about 2 min), `crossed` (about 2 min; tanh-sinh steps $\frac18$, $\frac1{16}$),
`corner` (about 4 min at `--level 4`, 15 min at the default `--level 8`, an hour at
`--level 16`), `crossedexact` (about 1 min), `cornerexact` (about 20 s).
