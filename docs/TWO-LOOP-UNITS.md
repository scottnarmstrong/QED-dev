# Two-loop units: low-dimensional integral representations of the q-type contributions

[Campaign HQ](../README.md) · [Two-loop derivation](TWO-LOOP-DERIVATION.md) ·
[Sources](SOURCES.md) · [Conventions](CONVENTIONS.md)

**Status (2026-11-18):** preparatory analysis for obligation O2-25 of
[TWO-LOOP-DERIVATION.md](TWO-LOOP-DERIVATION.md). Nothing here is a Lean declaration, and
nothing here is proved. Every representation below was derived from the covariant
Feynman-parametric integrand of section 11 of the derivation document and checked
numerically; the checks are evidence, not proof. The verification script is
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
| C | $-\ln\lambda+b_{\rm C}+o(1)$, $b_{\rm C}=2\int G_{\rm C}-\frac32$, eq. (6.5) | 3D; rational and $\ln$ (2D with $\mathrm{Li}_2$ after one more elementary integration) | 10 digits (outer step 1/8) | $\zeta(2)\ln2$, $\zeta(3)$ |
| S$+$C | $b_{\rm S}+b_{\rm C}$: the logarithms cancel inside the counterterms, eq. (7.1) | 1D $+$ 3D | 10 digits (outer step 1/8) | as for C |
| X | $\int_{\Delta_2}\Phi_{\rm X}(z_2,z_3)\,dz_2\,dz_3$, eq. (4.4) | 2D; rational, $\ln$, $\mathrm{Li}_2$ | 17 digits | $\zeta(2)\ln2$, $\zeta(3)$ |

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
Every $\mathrm{Li}_2$ argument is real and less than 1. $\Phi_{\rm X}$ has removable
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

The $x$-integral of $G_{\rm C}$ is elementary up to $\mathrm{Li}_2$: on $x<x_*$ the logarithms
are $\ln x$ and $\ln(Y^2+gx)$; on $x>x_*$ they are $\ln x$, $\ln(1-x)$ and, by the
factorization
$$Y^2(1-x)+y_3y_4x^2=y_3y_4\Bigl(\frac Y{y_3}-x\Bigr)\Bigl(\frac Y{y_4}-x\Bigr), \tag{6.6}$$
$\ln(Y/y_3-x)$ and $\ln(Y/y_4-x)$. The denominators are powers of $x$, $1-x$ and the same
linear factors. So $b_{\rm C}$ is a 2D integral of rational functions, logarithms and
$\mathrm{Li}_2$ of rational arguments, of the same type as (4.4) for X; the same comments
on the exact evaluation apply. Not carried out.

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
| X: value of (4.4) | one more analytic integration, then $\mathrm{Li}_3$ / $\mathrm{Li}_2\ln$ integrals reducing to the proved values at $\frac12$, $-1$, $1$ | high; the identities are not yet identified |
| C: value of $b_{\rm C}$ | the $x$-integral (6.6), then as for X | high |
| S$+$C | sum of the two, with the Ward-identity cancellation of 7 | as for C |

## 10. Sources and evidence

- Targets: BMR-I p. 852 (rendered page; rows b)–e)), totals p. 853.
- Parametric functions: CK-R (24)–(37), AKN (55)–(57), (64)–(65); the integrand itself is the
  one validated in section 11 of the derivation document.
- Cheng–Wu theorem, the masters $I_{j,n}$, the dilogarithm formula (4.3) and the special
  values $\mathrm{Li}_2(1)$: standard (**recalled**; the last is proved in `QED/Polylog/`).
- Everything else above is **derived** here and checked by
  `scripts/numerics/two_loop_unit_integrals.py`; nothing is proved.

Reproduce (single process each, niced): `exact` (seconds), `ladder` (under a minute),
`selfenergy` (about 2 min), `crossed` (about 2 min; tanh-sinh steps $\frac18$, $\frac1{16}$),
`corner` (about 4 min at `--level 4`, 15 min at the default `--level 8`, an hour at
`--level 16`).
