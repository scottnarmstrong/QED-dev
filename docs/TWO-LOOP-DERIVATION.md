# Two-loop derivation: the mass-independent fourth-order coefficient

[Campaign HQ](../README.md) · [Sources](SOURCES.md) · [Conventions](CONVENTIONS.md) ·
[Regularization](REGULARIZATION.md) · [One-loop derivation](ONE-LOOP-DERIVATION.md) ·
[Errata](ERRATA-AND-DEVIATIONS.md) · [Findings](campaign/FINDINGS.md) ·
[Decisions](campaign/DECISIONS.md)

**Status (2026-11-17):** source-linked derivation plan for Phase 4 (decision D-36), with
its proof obligations exposed. Nothing here is a Lean declaration, and nothing has been
approved, frozen, or proved. This is the two-loop analogue of
[ONE-LOOP-DERIVATION.md](ONE-LOOP-DERIVATION.md). Revised after an independent refute-first
review (2026-11-17), whose findings are folded in: the order of limits (section 5.6), new
obligations, and the AHKN errata (section 9). Notation and conventions are the
project's ([CONVENTIONS.md](CONVENTIONS.md)): mostly-plus metric, $e<0$, $q=p'-p$,
$r=\alpha/\pi=e^2/4\pi^2$, a Pauli–Villars photon of mass $\Lambda$, a photon mass
$m_\gamma$, Pauli–Villars regulator fermions of masses $M_1,M_2$ with closed-loop
coefficients $c_1,c_2$ (D-22), and energy-first loop integrals (D-5, M1).

Obligations are numbered **O2-1, O2-2, …**. As at one loop, each is something the project
must **prove**, or, where marked, **define** after author approval. None may be added as a
hypothesis of a source-facing theorem. Each claim below is labelled by its evidence:

- **source** — read in the pinned PDF at the cited place (rendered page checked where a
  formula is load-bearing);
- **numerics** — checked by a floating-point or multiprecision computation (section 10); this
  is evidence, not proof;
- **recalled** — standard knowledge not located in a pinned source; it must be pinned or
  proved before it is relied on.

Source abbreviations (all pinned in [SOURCES.md](SOURCES.md)): **BMR-I**, **BMR-II**
(`bmr-1972-I`, `bmr-1972-II`; page numbers are the journal's, 824–864 and 865–916),
**CK-R**, **CK-UV** (`ck-1974-rules`, `ck-1974-uvir`; journal pages 3978–4006), **AHKN**
(`ahkn-2012`; "p. $n$" is the PDF page $n$/36), **AKN** (`akn-2019`; "p. $n$" is page
$n$ of 27), **BMR04** (`bmr-2004`, arXiv v1), **Pet** (`petermann-1958`), **Pas**
(`passera-2007`), and Srednicki's draft for equation numbers $(n.m)$.

## 1. Target and its decomposition

The target is the coefficient of $r^2$ in the Pauli form factor at zero momentum transfer,
from diagrams with photons and a single lepton flavour:
$$A_1^{(4)}=\frac{197}{144}+\frac{\pi^2}{12}-\frac{\pi^2}{2}\ln2+\frac34\zeta(3)
=-0.328\,478\,965\,579\,193\,784\,582\ldots$$
It is stated in this form in Pas (9), and as $F_2^{(4)}(0)$ in BMR-I (1.7), p. 830,
and BMR-I p. 853 (source); BMR04 (117), section 7, gives the same constant term
$\tfrac{197}{144}+\tfrac12\zeta(2)-3\zeta(2)\ln2+\tfrac34\zeta(3)$ in dimensional
regularization (source). Here $\zeta(2)=\pi^2/6$.

It splits into two gauge-invariant parts:

| Part | Closed form | Value (numerics, 40 digits computed) |
| --- | --- | --- |
| Vacuum-polarization (VP) insertion, electron loop | $\frac{119}{36}-\frac{\pi^2}{3}$ | $+0.015\,687\,421\,859\,102\,682\,610\,725$ |
| No fermion loop ("$q$-type": ladder, crossed, two corners, two self-energy insertions) | $-\frac{31}{16}+\frac{5\pi^2}{12}-\frac{\pi^2}{2}\ln2+\frac34\zeta(3)$ | $-0.344\,166\,387\,438\,296\,467\,192\,898$ |
| Sum | $A_1^{(4)}$ | $-0.328\,478\,965\,579\,193\,784\,582\,173$ |

The sum of the two rows equals $A_1^{(4)}$ to all 40 computed digits; the rational parts
satisfy $\tfrac{119}{36}-\tfrac{31}{16}=\tfrac{197}{144}$ exactly. Agreement with
published values: Pas (9) prints $-0.328\,478\,965\,579\,193\,78\ldots$; AHKN (7.18) and AKN
(97) quote the $q$-type analytic value $-0.344\,166\cdots$ (source). The VP value is BMR-II
(1.10), p. 869, and BMR-I p. 852 (source).

BMR-I p. 852 (rendered page checked) also lists the contribution of each Feynman-graph
class, in Feynman gauge with a photon mass $\lambda$ and with every one-loop subgraph
renormalized on shell:

| Graph class (BMR-I Fig. 2) | $F_2^{(4)}(0)$ contribution (source) | Value without the log (numerics) |
| --- | --- | --- |
| a) VP insertion | $\frac{119}{36}-2\zeta(2)$ | $+0.015\,687\,421\,859$ |
| b) two self-mass insertions | $\frac{11}{24}-\frac13\zeta(2)+\ln\frac{\lambda}{m}$ | $-0.089\,978\,022\,283$ |
| c) two corner graphs | $-\frac{67}{24}+2\zeta(2)\ln2+\frac13\zeta(2)-\frac12\zeta(3)-\ln\frac{\lambda}{m}$ | $-0.564\,020\,941\,345$ |
| d) ladder | $\frac{11}{48}+\frac13\zeta(2)$ | $+0.777\,478\,022\,283$ |
| e) crossed ladder | $\frac16-5\zeta(2)\ln2+\frac{13}{6}\zeta(2)+\frac54\zeta(3)$ | $-0.467\,645\,446\,094$ |

The five rows sum to $A_1^{(4)}$ (checked exactly and to 30 digits). The logarithms cancel
between rows b) and c). These per-graph numbers depend on how the counterterms are
allotted to graphs; sections 5.2 and 5.5 explain why they are expected to be the limits of the
route-A "units" of section 5.2, which is to be proved, not assumed.

- **O2-1 (the target constant).** Define $A_1^{(4)}$ as an explicit real number built from
  `Real.pi`, `Real.log 2` and $\zeta(3)$ (as `riemannZeta 3` or as $\sum_{n\ge1}n^{-3}$; the
  two agree by `zeta_eq_tsum_one_div_nat_add_one_cpow`). Definition; low risk. The
  decomposition into the two parts is arithmetic.

## 2. What the frozen one-loop model provides, and what must change

The frozen model (`QED/Frozen/WickModel/`, packets 6a–6c, D-24–D-33) already has the
pieces that are order-independent:

- `Contraction`, `fermionSign`, `ClosedLoop`, `loopWeight`, `Flavoring`, `Preserves`,
  `regulatedAmplitude` (X₂₆), and the 1PI and connectivity predicates. By D-19.4 these are
  defined for any number of vertices of each kind.
- The regulated propagators `electronPropagator`, `photonPropagator` (packet 1) and the
  vertex factors of packet 5.
- The order-$e^2$ renormalization data at fixed regulators: the on-shell electron conditions
  (Z₅) with unique $(\delta_2,\delta_m)$ (Z₆), the photon condition $\Pi(0)=0$ (Z₈) with
  unique $\delta_3$ (Z₉), the charge condition (K₀) and its LSZ form (L₄), and the
  form-factor predicates `IsFormFactorPair` (G₀) and `IsLSZFormFactorPair` (H₀).

What is one-loop specific:

1. **Loop count.** `onePIFunction` and `connectedFunction` are source-facing only for
   $K\le2n_f+n_A+1$, which forces at most one loop. For a connected contraction with
   externals attached, let $V_3$ be the number of three-field vertices (`gauge`, `gaugeCt`).
   Counting fields gives
   $$L=\tfrac12V_3-n_f-\tfrac12n_A+1 .$$
   Each vertex has order at least one, so $V_3\le K$ and $L\le\tfrac12(K-2n_f-n_A)+1$. At
   most two loops occur exactly when $K\le2n_f+n_A+3$: the vertex ($n_f=n_A=1$) at $K=5$, the
   self-energy ($n_f=1,n_A=0$) and the vacuum polarization ($n_f=0,n_A=2$) at $K=4$.
2. **Routing.** `IsLoopLine` picks one chord and `lineMomentum` routes one loop momentum.
3. **Loop integral.** `contractionValue` integrates over one $\ell\in\mathbb R^4$ with the
   frozen `energyFirstIntegral` (D).
4. **Counterterms.** `Params` holds single real numbers $\delta_1,\delta_2,\delta_m,\delta_3$,
   and `VertexKind.order` fixes `gaugeCt` at order 3 and `fermionCt`, `photonCt` at order 2
   (D-19). At $K=5$ the counterterm `gaugeCt` occurs inside one-loop graphs, so a single real
   $\delta_1$ fixed by an exact truncated charge condition solves a rational, not a
   polynomial, equation in $e$ and produces spurious higher-order terms. The order-$e^4$
   parts must be separate data (section 8, question 2).
5. **Regulator fermions.** D-32 keeps $M_1,M_2$ fixed. At two loops they enter $F_2$
   through the VP insertion and must be removed by a limit $M_f\to\infty$ (D-36).

## 3. Stage 1 — Enumeration at order $e^5$

The object is the 1PI electron–electron–photon function (62.39) at total order exactly 5
(section 8, question 6), $n_f=n_A=1$.

### 3.1 Contractions without counterterms (five `gauge` vertices)

Five gauge vertices and $L=2$. Classify by closed fermion loops.

- **No closed loop.** The open line has five vertices $v_1,\dots,v_5$ in order, one of
  which, $v_j$, carries the external photon; the other four are paired by two photon lines.
  If $j\in\{1,5\}$, the line from $v_j$ inward is a bridge, so $j\in\{2,3,4\}$. Of the
  $3\times3$ pairings, one per value of $j$ leaves a bridge (a leg correction). The six
  1PI classes are:

  | Class | $j$ | Pairing | Name (BMR-I Fig. 2; AKN Fig. 2) |
  | --- | --- | --- | --- |
  | L | 3 | $(v_1v_5)(v_2v_4)$ | ladder |
  | X | 3 | $(v_1v_4)(v_2v_5)$ | crossed ladder |
  | C₊ | 2 | $(v_1v_4)(v_3v_5)$ | corner (vertex subgraph at $v_4$) |
  | C₋ | 4 | $(v_1v_3)(v_2v_5)$ | corner (vertex subgraph at $v_2$) |
  | S₊ | 2 | $(v_1v_5)(v_3v_4)$ | self-energy on the outgoing internal line |
  | S₋ | 4 | $(v_1v_5)(v_2v_3)$ | self-energy on the incoming internal line |

  In AKN's Ward–Takahashi grouping (AKN (29)–(30), p. 10–11), L, S₊, S₋ come from the
  rainbow self-energy $M_{4b}$, and X, C₊, C₋ from the crossing self-energy $M_{4a}$ (AKN
  Fig. 6 shows $M_{4a}$, $M_{4b}$).

  Reversing the open line ($v_i\mapsto v_{6-i}$, the **mirror**) exchanges C₊ with C₋ and
  S₊ with S₋, and maps L, X and the VP graph to themselves (checked on the pairings above).
- **One closed loop with two vertices** (VP insertion): the open line has three vertices,
  the middle one external. One contraction; the flavour sum over $f\in\{0,1,2\}$ with
  weights $c_f$ ($c_0=1$) sits inside its value (X₂₆, D-24).
- **One closed loop with three vertices, the external photon on the loop** (Furry
  triangles): two contractions, the two cyclic orientations of the loop.
- **Excluded by 1PI.** Tadpoles (a loop joined by one photon line, a bridge), loops with
  three or four vertices and the external photon on the open line, and two closed loops all
  contain a bridge or are disconnected.

### 3.2 Contractions with counterterms

With `gaugeCt` of order 3 and `fermionCt`, `photonCt` of order 2, order 5 allows:

| Counterterm | Placement | Classes | Effect |
| --- | --- | --- | --- |
| $\delta_1$ (`gaugeCt`) | any of the three vertices of the one-loop graph | 3 | $\delta_1\times$ one-loop vertex |
| $\delta_2,\delta_m$ (`fermionCt`) | either internal electron line of the one-loop graph | 2 | see O2-13 |
| $\delta_3$ (`photonCt`) | the internal photon line | 1 (two slot pairings, D-24) | see O2-13, O2-14 |
| $\delta_1^{(4)}$ (order-5 `gaugeCt`, new) | tree | 1 | $\gamma^\mu$ only |

Two counterterm vertices, or one counterterm with one gauge vertex, give only trees with
bridges. Order-$e^4$ parts of $\delta_2,\delta_m,\delta_3$ cannot appear in the 1PI vertex at
order 5 (their only contraction has a bridge). They are needed only for the LSZ form
(section 8, question 5).

The counterterm placements match the UV-divergent one-loop subgraphs one to one: the
three vertex subgraphs (the inner rung of L with the external vertex, and the subvertices of
C₊, C₋) to the three $\delta_1$ insertions, the two self-energy subgraphs of S₊, S₋ to the
two $(\delta_2,\delta_m)$ insertions, and the VP subgraph to $\delta_3$. X has no divergent
subgraph (BMR04 section 4: "with the exception of the Cross graph"; source).

### 3.3 Combinatorial factors and signs

`onePIFunction` sums over all kind sequences $\kappa$ and all contractions, with
$1/N!$. A 1PI vertex graph with distinguished external legs has no automorphism: the open
line is a path whose order is fixed by the externals, every photon line is pinned by its
ends, and a two-vertex loop attached to two distinct photon lines is fixed. Each class is
therefore produced by exactly $N!$ labelled contractions with the same value, and enters
with coefficient one. The `photonCt` factor is half the Feynman rule because its two
pairings are separate contractions (V₁₉). Signs: no closed loop gives $+1$ relative to the
tree; a closed loop gives $-1$ (X₅).

- **O2-2 (enumeration).** The order-5 1PI vertex at fixed $\varepsilon>0$ equals the sum
  of the nine contraction classes of 3.1 and the seven of 3.2, each with coefficient one and
  the stated sign. This generalizes packet 5's classification and (Y₁). Theorem; finite
  combinatorics, moderate size (the review notes that the cost of deciding the
  classification in Lean at $N=5$ may push it higher). Source: Srednicki ch. 58 rules;
  BMR-I Fig. 2; AKN Fig. 2 (seven vertex diagrams).
- **O2-3 (Furry pair).** The two flavour-summed orientations of the three-vertex loop cancel
  at fixed $\varepsilon$. Per-flavour values are not objects of the model: X₂₆ sums the
  flavours inside the integrand. Proof: charge conjugation, $C\gamma^\mu C^{-1}=-\gamma^{\mu T}$,
  turns one orientation's integrand into minus the other's with the loop momentum reflected
  and shifted, flavour by flavour, so the cancellation needs the reflection and shift
  invariance of the two-loop prescription (O2-6) on integrable data. Integrability needs the
  flavour sum: one flavour's triangle decays like $|\ell|^{-3}$, and with
  $\sum c_f=\sum c_fM_f^2=0$ the sum decays like $|\ell|^{-7}$ (power counting, section 4.1).
  Theorem; low–moderate risk.
- **O2-4 (tadpoles).** Tadpoles do not enter the 1PI function. For the connected and LSZ
  functions they vanish at fixed $\varepsilon$: the flavour-summed loop integrand
  $\sum_fc_f\,\mathrm{tr}[\gamma^\mu\tilde S_f(\ell)]$ is odd in $\ell$ and decays like
  $|\ell|^{-5}$. Theorem; low risk; needed only for the LSZ form.

## 4. Stage 2 — The regulated two-loop integrals (route A)

### 4.1 Power counting at fixed regulators

With the Pauli–Villars photon each internal photon line decays like $|k|^{-4}$. Euclidean
superficial degrees (integrand degree plus $4\times$loops):

| Subgraph | Degree | Comment |
| --- | --- | --- |
| electron self-energy | $-1$ | convergent (the integrand degree is $-5$; REGULARIZATION.md section 3) |
| vertex | $-2$ | convergent |
| VP loop, one flavour | $+2$ | not integrable alone |
| VP loop, flavour sum | $\le-2$ | $\sum c_f=0$ removes the mass-independent part at every order; $\sum c_fM_f^2=0$ the $M^2$ part; the trace has only even powers of $M_f$ |
| Furry triangle, flavour sum | $\le-3$ | same argument |
| two-loop vertex classes, overall | $-4$ (L: 4 electron, 2 photon lines) | convergent |
| VP-inserted vertex, overall | $\le-8$ | convergent |

By Weinberg's power-counting theorem (**recalled**, not pinned) every class is absolutely
convergent in the Euclidean sense. **No new Pauli–Villars condition arises at two loops**:
the two existing conditions already make every closed fermion loop at this order
convergent. Two side remarks that may simplify proofs:

- The Pauli–Villars photon is a mass integral,
  $\frac{1}{k^2+m_\gamma^2}-\frac{1}{k^2+\Lambda^2}
  =\int_{m_\gamma^2}^{\Lambda^2}\frac{d\mu}{(k^2+\mu)^2}$,
  so each photon line can be parametrized as a squared propagator with a compactly
  integrated mass, which removes the need to keep Pauli–Villars pairs together.
- The regulator-fermion sum annihilates affine functions of $M^2$. By Peano's kernel
  theorem it is $(M_1^2-m^2)(M_2^2-m^2)$ times the second divided difference of
  $g(\mu)$ at $m^2,M_1^2,M_2^2$, that is a positive B-spline average of $g''$. A flavour sum
  of a function of $\mu=M_f^2$ becomes one integral of $\partial_\mu^2g$, which decays faster
  by two powers of $\ell^2$, that is four powers of $|\ell|$.

### 4.2 Two loop momenta, routing and the order bound

- **O2-5 (two-loop routing).** Define the loop lines of a connected contraction with
  cyclomatic number 2 by a greedy rule extending D-19.3: the first is the lowest-labelled
  non-bridge line; the second is the lowest-labelled non-bridge line after deleting the
  first. The two deleted lines are the chords of a spanning tree. Line momenta are tree
  routing of external momenta plus $\ell_1,\ell_2$ along the fundamental cycles. Theorems:
  (i) the assignment is conserved at every vertex and unique given the chord momenta;
  (ii) a different choice of chords changes $(\ell_1,\ell_2)$ by an integer unimodular matrix
  plus a shift by external momenta; (iii) the formula
  $L=\tfrac12V_3-n_f-\tfrac12n_A+1$ and the source-facing bound $K\le2n_f+n_A+3$.
  Definition and theorems; moderate (graph combinatorics in the frozen `Joined` and
  `IsBridge` vocabulary). Source: Srednicki rule 8, p. 349; CK-R (11)–(16), p. 3980–3981
  (circuit matrix, incidence matrix).

### 4.3 The two-loop energy-first prescription

Write $\ell_s=(t_s,\vec v_s)$. Two prescriptions extend M1:

- **Joint:** $\displaystyle\int_{\mathbb R^6}d^3v_1\,d^3v_2\left(\int_{\mathbb R^2}dt_1\,dt_2\,
  f_\varepsilon\right)$, then $\varepsilon\to0^+$.
- **Nested:** `energyFirstIntegral` applied twice, $\int d^3v_2\int dt_2\int d^3v_1\int dt_1
  f_\varepsilon$.

**The analogue of finding F-1** (numerics, section 10). After Feynman parametrization the
combined denominator is $-t^{\mathsf T}At+w$ with $A=(U_{st})$ positive definite and
$w=\vec v^{\mathsf T}A\vec v+V-i\varepsilon$. At one loop, F-1 showed that the absolute
energy integral behaves like $1/(\omega\varepsilon^{n-1})$. At two loops it does not decay
at all in the spatial momenta: for $A=I$,
$$\int_{\mathbb R^2}\frac{dt}{\bigl|-|t|^2+R-i\varepsilon\bigr|^n}
=\pi\int_0^\infty\frac{du}{|R-u-i\varepsilon|^n}\ \longrightarrow\ \pi\,c_n\,\varepsilon^{1-n}
\quad(R\to\infty),$$
which is independent of $R$ (numerically $628.3$ for $n=3$, $\varepsilon=0.1$, at
$R=10,10^2,10^3$). So Tonelli fails on (energies) $\times$ (space) after parametrization,
more severely than at one loop, and any Fubini step there must use the signed energy integral.
The signed integral is elementary, with integer powers and no branch choice:
$$\int_{\mathbb R^2}\frac{dt_1\,dt_2}{(-t^{\mathsf T}At+w)^n}
=-\frac{\pi}{n-1}\,(\det A)^{-1/2}\,w^{1-n}\qquad(n\ge2,\ \operatorname{Im}w<0).$$
Proof: diagonalize $A$, pass to polar coordinates, and use the antiderivative of
$(w-u)^{-n}$; $w-u\ne0$ because $\operatorname{Im}w<0$. Checked numerically for $n=2,3$,
two values of $w$ and a non-diagonal $A$ (section 10). This replaces the holomorphy argument
of O-7. Note $\det A=U$, the first Symanzik polynomial (CK-R (24)).

Before parametrization the absolute two-loop integrand is better behaved, because each
propagator is bounded by $1/\varepsilon$ and decays. The energy integral at fixed spatial
momenta converges absolutely: every direction in $(t_1,t_2)$ meets enough decaying lines,
for example decay $|t|^{-5}$ in $t_2$ alone for S₊, $|t|^{-8}$ in $t_1$ alone, and
$|t|^{-12}$ overall.

- **O2-6 (the prescription and its invariances).** Define the joint prescription as an
  operation on $(\mathbb R^4)^2\to\mathbb C$ (the frozen (D) is its one-loop case). Prove that
  on integrable data it is invariant under integer unimodular changes of $(\ell_1,\ell_2)$
  that act equally on energies and space, under real shifts, and under the reflection
  $\ell\mapsto-\ell$. Definition (meaning-carrying, needs approval) and theorems; low–moderate.
- **O2-7 (well-definedness).** For each class of 3.1–3.2, with $m,m_\gamma,\Lambda>0$,
  $M_f>m$, the Pauli–Villars conditions, on-shell positive-energy $p,p'$ and $q^2\ge0$:
  the inner energy integral and the outer spatial integral are integrable for every
  $\varepsilon>0$, and the value has a unique limit as $\varepsilon\to0^+$. This is the
  two-loop analogue of packet 1's (E). Theorem; **high** effort; the main analytic risk of
  stage 2.
- **O2-8 (nested equals joint, for insertions).** For the insertion classes S₊, S₋ and VP,
  the joint value equals the outer one-loop integral of the frozen inner one-loop function
  (Σ, Π at fixed $\varepsilon$, then $\varepsilon\to0^+$, as appropriate). This is needed to
  reuse the frozen self-energy and vacuum polarization. Theorem; moderate–high (exchange of
  limits in $\varepsilon$ for the subloop and the outer loop).
- **O2-9 (embedding).** The analogue of (Y₁) for the successor model (order-labelled
  counterterm kinds or graded `Params`, two-loop routing, the joint prescription; section 7
  carriers): at total order at most 3 it reproduces packet 6a, that is the same contractions
  with the same values, the order-$e^2$ counterterm data and the frozen predicates (Z₅),
  (Z₈), (K₀); and the joint prescription of O2-6, applied to one-loop data, is the frozen
  (D). Without it the two-loop statements would not be about the frozen model. Theorem;
  low–moderate (mostly definitional, but the kind sequences summed over change).

### 4.4 Feynman parametrization at two loops

For a graph $G$ with $N$ internal lines, Feynman parameters $z_i$ on the simplex, and loop
matrix $\xi$ (CK-R (11)–(14); AHKN (4.23)–(4.25); AKN (50)–(54)):
$$U_{st}=\sum_iz_i\xi_{is}\xi_{it},\qquad U=\det(U_{st}),\qquad
B_{ij}=U\sum_{s,t}\xi_{is}\xi_{jt}(U^{-1})_{st},$$
$$A_i=1-\sum_jz_jB_{ij}/U\quad\text{on the electron path (AKN (55))},$$
with $G=\sum_iz_iA_i$ and $V=\sum_iz_i-G$ for $m=1$ and massless photons (AKN (56)–(57); the
general $V$ is CK-R (26), with photon-mass terms as in AKN (34)). The
momentum integral is CK-R (30)–(31); the numerator contraction rule is CK-R rule 6, (7)
and (37), and AKN (64)–(65). For the crossing graph AKN (58)–(59) give
$U=z_{1a}z_2+z_{1a}z_{3b}+z_2z_{3b}$ and the $B_{ij}$; we checked these against the loop
matrix independently (section 10).

- **O2-10 (parametrization inside the energy integral).** At fixed $\vec v$ and
  $\varepsilon>0$: the generalized Feynman formula (AKN (32)) for $N=6$ denominators (or
  with squared photon denominators, section 4.1); Fubini on simplex $\times\mathbb R^2$; the
  energy shift; then the 2D formula of 4.3 and the 6D spatial formula
  $\int_{\mathbb R^6}(\vec v^{\mathsf T}A\vec v+w)^{-k}d^6v=\pi^3\frac{\Gamma(k-3)}{\Gamma(k)}
  (\det A)^{-3/2}w^{3-k}$ (**recalled**). The one-loop analogues are proved
  (`QED/Integration/FeynmanParameter.lean`, `EnergyIntegral.lean`). Theorem; moderate.
  The degenerations $U\to0$ at the simplex faces are exactly the UV subdivergences (CK-UV
  (2.3), (2.11), p. 3992–3993); at fixed $\Lambda,M_f$ the regulators make them integrable,
  but only after the Pauli–Villars pairs are combined (or rewritten as in 4.1).
- **O2-11 (numerator algebra and projection to $F_2$).** The parametric numerator of each
  class: the loop momenta in the numerator replaced by contractions in the $B_{ij}$ and the
  powers of $V$ lowered accordingly (CK-R rule 6, (7), (37); AKN (64)–(65)); and a
  projector $P_2$, a linear map on the vertex value at on-shell $(p,p')$ that returns $F_2$
  whenever the value has the form (G₀). AKN (47)–(49) project the Ward–Takahashi-summed
  self-energy form at $q\to0$; at $q\ne0$ a trace projector on the spinor bases is the
  candidate (**recalled**). Per-class $F_2[G]$ (section 5.1) is defined through $P_2$, since
  a single class need not have the form (G₀) (O2-21). Definition and theorems; moderate.
- **O2-12 (positivity of $V$).** On the closed simplex, for on-shell $p,p'$ with $q^2\ge0$
  and $m_\gamma>0$, $V$ is bounded below by a positive constant. This is the two-loop
  analogue of $D\ge(1-x_3)^2m^2+x_3m_\gamma^2$ ("no thresholds": a free electron cannot
  emit a massive photon). It gives the $\varepsilon\to0^+$ limit of O2-7 by dominated
  convergence. CK-UV (4.3)–(4.7), p. 3999, write $V$ on the electron path as
  $\sum z_i(1-A_i)$ plus photon-mass terms, with $A_i$ a current fraction. Theorem;
  **moderate–high risk**: a uniform lower bound, including at faces where $U\to0$, is
  unproved and has not been located in a pinned source. O2-22 needs it uniformly for small
  $q^2\ge0$.

## 5. Stage 3 — Subtraction at fixed regulators

Everything in this stage happens at fixed $m_\gamma,\Lambda,M_f$ and after
$\varepsilon\to0^+$, where every class is finite. "Subtraction" means grouping each
divergent subgraph with its counterterm insertion and proving identities between finite
quantities. It does not mean defining new objects by subtraction.

### 5.1 Counterterm insertion identities

Write $\delta_i=e^2d_i+O(e^4)$, with $d_i$ the order-$e^2$ coefficients fixed by (Z₆),
(Z₉) and the charge condition (K₀) (or its LSZ form (L₄)). The vertex factor of
`fermionCt` is $-i(\delta_2\not k+\delta_mm)$ (V₁₉). Since
$(\not k+m)(-\not k+m)=k^2+m^2$,
$$\tfrac1i\tilde S\,[-i(\delta_2\not k+\delta_mm)]\,\tfrac1i\tilde S
=\tfrac1i\Bigl[-\delta_2\tilde S+(\delta_2-\delta_m)\,m\,\tilde S^2\Bigr]+O(\varepsilon).$$
The $O(\varepsilon)$ comes from
$(\not k+m)\tilde S_\varepsilon=1+i\varepsilon/(k^2+m^2-i\varepsilon)$.
It is not zero at fixed $\varepsilon$, so the identity holds only in the limit. The
`photonCt` insertion (both pairings) replaces the regulated photon factor
$D(k)=\frac1{k^2+m_\gamma^2}-\frac1{k^2+\Lambda^2}$ by $-\delta_3k^2D(k)^2$, plus
$k^\mu k^\nu$ terms, which reach $F_1$ only (O2-14). A `gaugeCt` insertion multiplies the
graph by $\delta_1$. Hence, for the coefficient of $e^4$ in $F_2$ (with the Furry pair
cancelling, O2-3):
$$[e^4]F_2=\sum_{G\in\{\mathrm L,\mathrm X,\mathrm C_\pm,\mathrm S_\pm,\mathrm{VP}\}}F_2[G]
+(3d_1-2d_2)\,F_2^{(2)}+(d_2-d_m)\,F_2^{*}-d_3\,F_2^{(\gamma)} .$$
Here $F_2^{(2)}$ is the one-loop Pauli coefficient, $F_2^{*}$ the sum over the two internal
electron lines of the mass-insertion graphs ($\tilde S\to m\tilde S^2$), and $F_2^{(\gamma)}$
the one-loop graph with $D\to k^2D^2$. All are at fixed regulators. A single class need not
have the form (G₀) (O2-21), so $F_2[G]$ for one class means the projection $P_2$ of O2-11;
on the mirror-closed units of 5.2 it is the Pauli component of (G₀).

- **O2-13 (insertion identities).** The three identities above, in the $\varepsilon\to0^+$
  limit, as statements about the values of the counterterm classes. Theorem; low–moderate
  (dominated convergence for the $O(\varepsilon)$ term). Source: Srednicki (62.2)–(62.3);
  CK-UV (3.24)–(3.28), p. 3996–3997 (the parametric form, using Nakanishi's identity CK-R
  (81)–(85), p. 3986).
- **O2-14 (longitudinal terms).** The $k^\mu k^\nu$ terms of the `photonCt` insertion, and
  those of the VP insertion (the $k^\mu k^\nu$ part of $\Pi^{\mu\nu}(k)$ in (62.10)),
  contribute to $F_1$ only, in the $\varepsilon\to0^+$ limit. Contracted into the open line,
  $k^\mu$ gives $\not k$, which on shell cancels the adjacent propagators (the line-by-line
  Ward identity), but only up to $O(\varepsilon)$, since
  $\tilde S_\varepsilon^{-1}\ne\not p+m$ at $\varepsilon>0$ (compare O2-15). Theorem;
  low–moderate (**recalled** mechanism, not located in a pinned source).
- **O2-15 (the Ward identity at one loop).** At fixed $m_\gamma,\Lambda$: if the electron is
  on shell (Z₅) and the charge condition (K₀) holds, then $\delta_1^{(2)}=\delta_2^{(2)}$. Proof
  route: the differential identity $\partial\tilde S/\partial p_\mu=-\tilde S\gamma^\mu\tilde S$,
  differentiation under the one-loop integral, and the relation of the $q\to0$ vertex to
  $\partial\Sigma/\partial p$. At $\varepsilon>0$ the identity has an $O(\varepsilon)$
  defect, since $\tilde S_\varepsilon^{-1}=(\not p+m)(p^2+m^2-i\varepsilon)/(p^2+m^2)$ is not
  affine in $p$; it is therefore proved in the $\varepsilon\to0^+$ limit, or directly on the
  parametric closed forms. Only the
  photon line is regulated, and the identity holds line by line on electron lines, so the
  Pauli–Villars photon preserves it (REGULARIZATION.md, route B row). Theorem; moderate.
  Source: Srednicki (68.13) (statement); AKN (29)–(30) and AHKN (4.29)–(4.30) (the
  Ward–Takahashi identity used to sum vertex graphs); BMR04 section 4 ("$Z_2^{(1l)}=-Z_1^{(1l)}$
  due to the Ward identity", their sign convention). See section 8, question 1.

With O2-15, the $\delta$-terms reduce to $d_1F_2^{(2)}+(d_2-d_m)F_2^*-d_3F_2^{(\gamma)}$.

### 5.2 Units and their UV cancellation

Define five **units**, each a graph class together with the counterterm insertions on its
divergent subgraphs (section 3.2):

| Unit | Content | UV subdivergence at $\Lambda\to\infty$ | Cancelled by |
| --- | --- | --- | --- |
| VP | VP graph (flavour-summed) $+$ $\delta_3$ insertion | none at fixed $M_f$; with $M_f\to\infty$, $\ln M_f$ | $\delta_3$ via $\Pi(0)=0$ (5.3) |
| S | S₊ $+$ S₋ $+$ their $(\delta_2,\delta_m)$ insertions | self-energy, $\ln\Lambda$ | $\delta_2$ and $\delta_m$ |
| C | C₊ $+$ C₋ $+$ $\delta_1$ at their internal vertices | vertex, $\ln\Lambda$ | $\delta_1$ |
| L | ladder $+$ $\delta_1$ at the external vertex | inner vertex, $\ln\Lambda$ | $\delta_1$ |
| X | crossed ladder | none | — |

Each unit is closed under the mirror of 3.1, which is what O2-21 needs to give each unit a
form-factor pair of its own.

The overall divergence of the two-loop vertex is proportional to $\gamma^\mu$ and is absorbed
by $\delta_1^{(4)}$, so it does not reach $F_2$ (CK-UV p. 3995: the overall degree;
AKN p. 17: "it does not suffer from an overall divergence ... dropped when the anomalous
magnetic moment contribution is projected out").

- **O2-16 ($\delta_1^{(4)}$ and $F_1$).** The order-5 tree counterterm is a multiple of
  $\gamma^\mu$ and contributes to $F_1$ only (the analogue of O-8). Theorem; trivial.
- **O2-17 (UV cancellation per unit).** For each unit, its contribution to $[e^4]F_2$ at
  fixed $m_\gamma$ (and, for VP, fixed $M_f$) has a finite limit as $\Lambda\to\infty$. The
  standard proof is parametric: as the parameters of a divergent subgraph $S$ scale to zero,
  $U\to U_SU_{G/S}$, $B_{ij}\to B^S_{ij}U_{G/S}$, $A_i\to A_i^{G/S}$ (CK-UV (2.11)–(2.17),
  p. 3993; AHKN (5.6)–(5.22)), and the leading term factorizes into (subgraph renormalization
  constant) $\times$ (lower-order magnetic moment) (CK-UV (3.32), p. 3997; AKN (72), (79)).
  In route A, $\Lambda$ cuts off the $U\to0$ region, and the counterterm insertion supplies
  the same leading term with the on-shell constant in place of its UV part. Theorem;
  **high** effort. The cleanest route may avoid the $K$-operation altogether: route A
  needs only the difference "unit minus nothing", not a pointwise-finite integrand. The
  $K$-operation (CK-UV (2.8), (2.19)–(2.25)) is a device for numerical integration that
  avoids the infrared problems of on-shell subtraction (CK-UV p. 3992–3993; AKN p. 17).
  Route A has a photon mass and fixed regulators, so it does not need it.

### 5.3 Why $\Pi(0)=0$ becomes load-bearing

At one loop D-32 held for every $\delta_3$: the photon is an external field, and the
photon-leg term carries $q^2/(q^2+m_\gamma^2)$, which vanishes as $q\to0$ at fixed
$m_\gamma$. At order $e^5$ the vacuum polarization also sits on an **internal** line. By
(62.10) the first-order correction to the transverse photon factor is
$D\to D+\Pi(k^2)\,k^2D^2$, where $\Pi$ is the frozen vacuum polarization function (Z₇) with
$-\delta_3$ included. Writing $\Pi(k^2)=[\Pi(k^2)-\Pi(0)]+\Pi(0)$:
$$F_2[\mathrm{VP}+\delta_3]=F_2\bigl[D\to\Pi_R(k^2)k^2D^2\bigr]+\Pi(0)\,F_2^{(\gamma)},\qquad
F_2^{(\gamma)}\to\tfrac1{8\pi^2}\ (m_\gamma\to0,\ \Lambda\to\infty).$$
The second term is nonzero unless $\Pi(0)=0$, and it is not bounded as $M_f\to\infty$,
because the unsubtracted regulated $\Pi(0)$ grows like $\ln M_f$ (recalled). The limit of
$k^2D^2$: $k^2/(k^2+m_\gamma^2)^2=1/(k^2+m_\gamma^2)-m_\gamma^2/(k^2+m_\gamma^2)^2$, and the second
term contributes $m_\gamma^2\,\partial_{m_\gamma^2}F_2^{(2)}=O(m_\gamma/m)$, by the one-loop
deficit bound of REGULARIZATION.md section 6. So the photon condition (Z₈) is a premise of
the two-loop result, and the "for every $\delta_3$" of D-32 does not carry over (D-36,
source: the decision record).

- **O2-18 (VP unit).** With (Z₈), $\Pi_R=\sum_fc_f\Pi_{R,f}$, and for each flavour $f$
  $$\Pi_{R,f}(k^2)=\frac{e^2}{2\pi^2}\int_0^1dx\,x(1-x)\ln\frac{M_f^2+x(1-x)k^2}{M_f^2}
  =\frac{e^2}{4\pi^2}\int_0^1dv\,\rho(v)\,\frac{k^2}{k^2+4M_f^2/(1-v^2)},$$
  with $M_0=m$ and $\rho(v)=v^2(1-v^2/3)/(1-v^2)$. The first form is Srednicki (62.25),
  p. 372, at $M_f=m$ (source); it is positive for $k^2>0$. The second, spectral, form is
  **recalled**; its equality with the first is an elementary integral identity, checked
  numerically (ratio $1$ to 20 digits at $k^2=0.3$ and $5$, section 10). At $m_\gamma=0$,
  $\Lambda=\infty$, where $D=1/k^2$, it gives
  $\Pi_{R,f}k^2D^2=\frac{e^2}{4\pi^2}\int_0^1dv\,\rho(v)/(k^2+\mu_v^2)$ with
  $\mu_v=2M_f/\sqrt{1-v^2}$: the VP-inserted photon line is **replaced** by a
  $v$-superposition of massive photon lines of mass $\mu_v$, and the VP unit becomes a
  superposition of one-loop vertices. The superposition is exact only at $m_\gamma=0$,
  $\Lambda=\infty$; at finite regulators $k^2D^2$ is not a single propagator, and the
  difference must be shown to vanish in the regulator limit, as in the computation above.
  Theorem; moderate. Its limit for the electron flavour is
  $$\int_0^1dv\,\frac{v^2(1-v^2/3)}{1-v^2}\int_0^1dx\,\frac{x^2(1-x)}{x^2+(1-x)\,\frac{4}{1-v^2}}
  =\frac{119}{36}-\frac{\pi^2}{3}$$
  (numerics: 40 digits). The inner integral is the one-loop $F_2/r$ with photon mass
  $\lambda$, $\lambda^2/m^2=4/(1-v^2)$; it is the same function as $C_1$ in
  REGULARIZATION.md section 6. BMR-II (1.1)–(1.10), p. 868–869, derives the same value
  dispersively (source). The exact evaluation needs only $\zeta(2)$.
- **O2-19 (regulator-fermion decoupling).** The flavours $f=1,2$ contribute
  $c_1g(M_1^2)+c_2g(M_2^2)$, where $g(\mu)$ is the VP-unit contribution of one flavour of
  squared mass $\mu$. A bound on $|g|$ alone does not suffice: $M_1=M_2$ is impossible when
  $M_f>m$ (the two Pauli–Villars conditions would force $M_f=m$), and $c_1,c_2$ blow up as
  $M_2\to M_1$. Solving the conditions,
  $c_1=(M_2^2-m^2)/(M_1^2-M_2^2)$ and $c_2=(M_1^2-m^2)/(M_2^2-M_1^2)$, so with
  $h(\mu)=g(\mu)/(\mu-m^2)$
  $$c_1g(M_1^2)+c_2g(M_2^2)=(M_1^2-m^2)(M_2^2-m^2)\,h[M_1^2,M_2^2]
  =(M_1^2-m^2)(M_2^2-m^2)\int_0^1h'\bigl(M_2^2+\theta(M_1^2-M_2^2)\bigr)\,d\theta ,$$
  a divided difference. The obligation is therefore a **derivative bound**, for example
  $|h'(\mu)|\lesssim m^2\mu^{-3}\ln(\mu/m^2)$ for $\mu$ beyond a threshold, uniformly in
  $m_\gamma\in(0,m]$ and $\Lambda$ (it follows from
  $|g|\lesssim(m^2/\mu)\ln(\mu/m^2)$ together with
  $|g'|\lesssim(m^2/\mu^2)\ln(\mu/m^2)$), which makes the contribution tend to $0$ as
  $\min M_f\to\infty$ with no constraint on $M_2/M_1$. (A heavy lepton of mass $M$
  contributes about $\tfrac1{45}(m/M)^2$ to $A_2^{(4)}$; **recalled**, consistent with Pas.)
  Theorem; moderate.

### 5.4 Form factors at order 5

- **O2-20 (covariance).** After $\varepsilon\to0^+$, at fixed regulators, the value of each
  unit at on-shell $(p,p')$ is Lorentz covariant. This is not free: the energy-first
  prescription singles out a frame, and its value at $\varepsilon>0$ is frame-dependent.
  Covariance must come through the parametric form of O2-10, where after the energy and
  spatial integrals the result depends on $p,p'$ only through invariants and $\not p,\not p'$
  (CK-R (30)–(31)). Theorem; moderate–high.
- **O2-21 (no $q^\mu$ term; decomposition).** For on-shell $p\ne p'$ with $q^2>0$, the
  order-5 1PI vertex (after $\varepsilon\to0^+$) has a unique pair $(F_1,F_2)$ in the sense of
  `IsFormFactorPair` (G₀), and so does each unit of 5.2. Covariance (O2-20) and the Gordon
  identity leave three structures, $\gamma^\mu$, $i\sigma^{\mu\nu}q_\nu$ and $q^\mu$, between
  the spinors. A single class such as C₊ or S₊ can carry a $\bar u'q^\mu u$ term, which
  (G₀) does not allow. It cancels only in the mirror pairs C₊ $+$ C₋ and S₊ $+$ S₋ (with
  their counterterm insertions), within the self-mirror classes L, X and VP (charge
  conjugation, **recalled**), or through the order-5 Ward identity $q_\mu V^\mu=0$ on shell.
  Uniqueness reuses packet 2's argument. Existence and uniqueness theorem; **moderate–high**.
- **O2-22 ($q^2\to0^+$ at fixed regulators).** At fixed $m_\gamma>0$, $\Lambda$, $M_1,M_2$
  and the on-shell order-$e^2$ counterterms, the Pauli coefficient $\hat F_2$ of the order-5
  vertex (question 6) has a limit as $q^2\to0^+$, uniformly over the on-shell pairs: there is
  exactly one number $a$ such that for every $\eta>0$ there is $q_0>0$ with
  $|\hat F_2-a|<\eta$ for every pair with $0<q^2<q_0$. By O2-20, $\hat F_2$ depends on the
  pair only through $q^2$, so uniformity reduces to a one-variable limit. The proof is
  continuity of the parametric representation at $q=0$ with $m_\gamma>0$, by dominated
  convergence, using O2-12 uniformly for small $q^2$. The number $a$ defines the regulated
  coefficient $F_2^{(4)}(0;m_\gamma,\Lambda,M_1,M_2)$, with a characterization theorem.
  $\exists!$ theorem, then definition; moderate. It is needed because the regulator limit
  must be taken after $q^2\to0^+$ (5.6).

### 5.5 Infrared structure

At fixed $m_\gamma>0$ every unit is finite. As $m_\gamma\to0$:

- **Linear divergences** ($\propto m/m_\gamma$) arise in S from the mass insertion
  ($\tilde S^2$ on a line adjacent to an on-shell external line). They cancel inside S
  because of $\Sigma(-m)=0$ (Z₅), between the self-energy graphs and the whole
  $(d_2-d_m)$ mass-insertion term of 5.1, not the $\delta_m$ insertion alone. AKN (85)–(86),
  p. 20, and AHKN section 6 (R-subtraction) describe the same mechanism in parametric form;
  CK-UV (4.21) and the text after it (p. 4001–4002) give the power counting.
- **Logarithmic divergences at $q^2=0$** (source). BMR-I p. 852 shows $+\ln(\lambda/m)$ in
  the self-mass pair and $-\ln(\lambda/m)$ in the corner pair, and no logarithm in the
  ladder or crossed graphs. BMR-I p. 834 states: a) the VP graph has no infrared divergence;
  b) the self-mass and corner graphs together have none; c) the ladder and crossed graphs
  together do, and it is the infrared divergence of the whole fourth order. The overall
  divergence is BMR-I (1.20) and the text after it, p. 834–835: $\ln\lambda\cdot
  B(t)F_2^{(2)}(t)$ with $B(0)=0$. So L and X are infrared finite **at $q^2=0$ only**; at
  $q^2\ne0$ their sum carries a logarithm (5.6).
- **A heuristic for the S–C cancellation** (not a derivation). If the infrared part of
  $\delta_1^{(2)}=\delta_2^{(2)}$ is $-r\ln(\lambda/m)$ (**recalled**, standard on-shell
  value) and $F_2^{(2)}(0)=r/2$, the counterterm terms of S contain
  $-2\delta_2F_2^{(2)}\ni+r^2\ln(\lambda/m)$ and those of C contain
  $+2\delta_1F_2^{(2)}\ni-r^2\ln(\lambda/m)$, which cancel only because $\delta_1=\delta_2$
  (O2-15). AKN (91)–(95), p. 21–22, show a cancellation of this kind in the $K$-scheme:
  $L_2^R+B_2^R$ is finite "because of the Ward–Takahashi identity". But the bare graphs carry
  infrared logarithms of their own (possibly also $\ln^2$ in single graphs), so this
  bookkeeping does not predict BMR's rows. The L unit shows it: it contains
  $+d_1F_2^{(2)}$, which contributes $-\tfrac12r^2\ln(\lambda/m)$, yet BMR's ladder has no
  logarithm, so the bare ladder must carry $+\tfrac12r^2\ln(\lambda/m)$. The cancellation must
  be proved unit by unit, from infrared expansions (O2-23).
- **O2-23 (infrared limit).** Plan: per-unit infrared expansions at $q^2=0$. For each unit
  $U$, its contribution to the regulated $F_2^{(4)}(0)$ of O2-22 has the form
  $a_U\ln(m_\gamma/m)+b_U(\Lambda,M_f)+o(1)$ as $m_\gamma\to0^+$, with the $o(1)$ uniform in
  $\Lambda,M_f$ beyond thresholds (or combined with O2-17 in the joint limit); then
  $a_{\mathrm L}=a_{\mathrm X}=a_{\mathrm{VP}}=0$ (BMR-I p. 834, item a), and p. 852),
  and $a_{\mathrm S}+a_{\mathrm C}=0$ by O2-15. Conclusion: the regulated $F_2^{(4)}(0)$ has
  a limit as $(m_\gamma,\Lambda,M_1,M_2)\to(0,\infty,\infty,\infty)$ jointly. Theorem;
  **high** effort. BMR-II (1.23)–(1.33), p. 873–875, shows that for the ladder the
  $\lambda\to0$ limit does not commute with the dispersive integration (source): route A
  must keep $m_\gamma>0$ until after the parametric integrals are combined, as D-36 says.

### 5.6 Order of limits and the headline (proposed, pending the author's ruling)

**The joint limit in $q^2$ and $m_\gamma$ does not exist at order $e^5$.** The frozen
one-loop headlines (I) and (H) take $q^2\to0^+$ jointly with the regulator limit, one $\delta$
bounding both $q^2$ and $m_\gamma$. That pattern cannot be copied. At $q^2\ne0$ the
order-$e^4$ Pauli form factor has an infrared logarithm $\ln(\lambda/m)\,B(t)F_2^{(2)}(t)$,
with $B(0)=0$ but $B(t)\ne0$ for $t\ne0$ (BMR-I (1.20), p. 834), carried by ladder plus
crossed (BMR-I p. 834, item c), source). BMR04 (117) shows the same in dimensional regularization:
$F_2^{(2l)}$ has an infrared pole $-q^2/\bigl(6(D-4)\bigr)$ at order $q^2$ (source). Near
$t=0$, $|B|\approx q^2/(3m^2)$ (the small-$t$ expansion of BMR-I (1.18a); **recalled**), so
$[r^2]F_2$ contains about $(q^2/6m^2)\ln(m/m_\gamma)$, using $F_2^{(2)}(0)=\tfrac12$; the
coefficient agrees with BMR04's pole under the standard correspondence
$1/(D-4)\leftrightarrow\ln(\lambda/m)$ (**recalled**). With $q^2=\delta m^2/2$ and
$m_\gamma=m\,e^{-100/\delta}$ this term is about $8$, so no choice of $(\delta,R)$ works.

**Proposed order.** $\varepsilon\to0^+$ at fixed everything; then $q^2\to0^+$ at fixed
regulators, uniformly over on-shell pairs (O2-22); then
$(m_\gamma,\Lambda,M_1,M_2)\to(0,\infty,\infty,\infty)$ jointly, with $c_1,c_2$ fixed by the
Pauli–Villars conditions. This is D-5's iterated order. The magnetic-moment definitions
of the frozen model (the response moments (R₀) and (L₅), and the source moment (L₇) with
its packet limit) already take $q\to0^+$ at fixed regulators, so they are unaffected; only
the Pauli-component clause changes shape.
Two shapes of headline:

- **(a) Quantifier form.** For every $\eta>0$ there are $\delta>0$ and $R$ such that for all
  regulators with $m_\gamma<\delta$ and $\Lambda,M_1,M_2>R$, and all admissible counterterms
  (the order-$e^2$ data satisfying (Z₅), (Z₈), (K₀); every $d_1^{(4)}$), there is
  $q_0>0$, depending on the regulators, such that every form-factor pair of $V^{\mu,[5]}$ at
  every on-shell pair with $0<q^2<q_0$ has $|16\pi^4\hat F_2-A_1^{(4)}|<\eta$.
- **(b) Recommended.** Three declarations: the $\exists!$ theorem of O2-22 (the
  $q^2\to0^+$ limit of $\hat F_2$ exists at fixed regulators); the definition of the
  regulated $F_2^{(4)}(0;m_\gamma,\Lambda,M_1,M_2)$ as that number, with its
  characterization; and the regulator limit
  $16\pi^4F_2^{(4)}(0;\cdot)\to A_1^{(4)}$ as $(m_\gamma,\Lambda,M_1,M_2)\to
  (0,\infty,\infty,\infty)$. Shape (b) implies (a), separates the two limits, and gives the
  regulated two-loop number a name that later phases can reuse.

The order of limits is a proposal; it needs the author's ruling (section 8, questions 3
and 6).

## 6. Stage 4 — Exact evaluation

D-36.3 asks for the exact closed form, with the finite subtracted integrals evaluated
analytically. The constants that occur are $1,\ \zeta(2)=\pi^2/6,\ \zeta(2)\ln2,\ \zeta(3)$.
Per-graph intermediate results in the dispersive method also contain $\ln^22$, $\ln^42$,
$\zeta(2)\ln^22$, $\mathrm{Li}_4(1/2)$ and $\zeta^2(2)$, which cancel between cut graphs
(BMR-II (1.74), p. 884, a ladder two-body cut, and (2.72), p. 907–908; source). The
dispersive discontinuities need the Nielsen functions $\mathrm{Li}_2,\mathrm{Li}_3,S_{1,2}$
at arguments $\pm x$, $x^2$ (BMR-I p. 826–827 and Appendix A; source).

**What Mathlib has** (pinned checkout, grep only): `hasSum_zeta_two` and `riemannZeta_two`
($\zeta(2)=\pi^2/6$), `riemannZeta_four`, the series form of `riemannZeta` for
$\operatorname{Re}s>1$, $\int\log\sin$ (`integral_log_sin_zero_pi_div_two`), and elementary
log and power integrals (MATHLIB-INVENTORY.md 3.7). **There is no dilogarithm,
polylogarithm or Nielsen function**, and no closed form is expected for $\zeta(3)$.

- **O2-24 (polylogarithm infrastructure).** Define $\mathrm{Li}_2,\mathrm{Li}_3$ on $[-1,1]$
  (series, or iterated integrals of $\log$), and prove: $\mathrm{Li}_2(1)=\zeta(2)$,
  $\mathrm{Li}_2(-1)=-\tfrac12\zeta(2)$, $\mathrm{Li}_2(\tfrac12)=\tfrac12\zeta(2)-\tfrac12\ln^22$,
  $\mathrm{Li}_3(1)=\zeta(3)$, $\mathrm{Li}_3(-1)=-\tfrac34\zeta(3)$,
  $\mathrm{Li}_3(\tfrac12)=\tfrac78\zeta(3)-\tfrac12\zeta(2)\ln2+\tfrac16\ln^32$, the
  reflection $\mathrm{Li}_2(x)+\mathrm{Li}_2(1-x)=\zeta(2)-\ln x\ln(1-x)$, and the
  definite integrals that the reduction produces, for example
  $\int_0^1\ln x\ln(1+x)\,dx/x=-\tfrac34\zeta(3)$. The values at $\tfrac12$ and the last
  integral are checked numerically (section 10); the identities are classical (**recalled**).
  Infrastructure; moderate (FTC with singular endpoints, Abel summation at $x=\pm1$).
- **O2-25 (exact values of the units).** Prove the limits, at $q^2=0$ (after O2-22),
  $$\mathrm X\to\tfrac16-5\zeta(2)\ln2+\tfrac{13}6\zeta(2)+\tfrac54\zeta(3),\qquad
  \mathrm L\to\tfrac{11}{48}+\tfrac13\zeta(2),$$
  $$\mathrm S+\mathrm C\to-\tfrac73+2\zeta(2)\ln2-\tfrac12\zeta(3),$$
  and VP as in O2-18. These are the BMR-I p. 852 values (S and C combined, so that the
  logarithms cancel); they sum to the $q$-type value. **Highest risk of the phase.**
  Theorem, one per unit. It is not yet known whether the route-A units have exactly these
  limits: BMR assign each graph its subgraphs renormalized on shell, which matches the
  units of 5.2, but they work dispersively with $\lambda$ only and without Pauli–Villars.
  A cheap high-precision numerical check of each unit in route A form is recommended
  before any declaration is drafted. **Infrared cost:** S and C are not separately finite
  as $m_\gamma\to0$. Each must be evaluated at $m_\gamma>0$ in the form
  $a\ln(m_\gamma/m)+b+o(1)$, with $b$ exact (the expansion of O2-23), and only the sum has an
  $m_\gamma$-free limit. Splitting off the logarithm exactly before evaluating the remainder
  is harder than evaluating a finite integral. L and X are evaluated at $q^2=0$, where they
  are infrared finite (5.5). Method options:
  1. **Parametric** (route A proper): reduce each unit to integrals over the simplex, as in
     the historical exact evaluations of Petermann and Sommerfield (BMR-I footnote 2,
     p. 825: Petermann, Helv. Phys. Acta 30 (1957) 407; Sommerfield, Ann. Phys. 5 (1958) 26).
     **Neither is pinned.** No pinned source gives an exact Feynman-parametric evaluation of
     the $q$-type set; AHKN and AKN evaluate the parametric integrals numerically.
  2. **Insertion form:** for S and VP, insert the closed-form one-loop $\Sigma_R$ and $\Pi_R$
     (O2-8, O2-18) and reduce to two-dimensional integrals of rational functions and logs.
     This is natural for VP; for S it needs the off-shell renormalized $\Sigma_R$ closed form.
  3. **Dispersive** (BMR): exact, fully worked in the pinned BMR-I/II, but it needs analytic
     continuation in $t$, Cutkosky cuts and subtracted dispersion relations with the
     $\lambda\to0$ subtleties of BMR-II section 1.3. This is a different mathematical theory
     from route A; it is useful as a map of which polylogarithm identities are needed.
- **O2-26 (assembly).** $16\pi^4F_2^{(4)}(0;m_\gamma,\Lambda,M_1,M_2)\to A_1^{(4)}$ in the
  order of limits of 5.6 (shape (b); shape (a) follows). Since $r=e^2/4\pi^2$,
  $[r^2]F_2=16\pi^4[e^4]F_2$. Theorem by combination; low once O2-1–O2-25 hold.

## 7. Obligations, carriers and kinds

The last column lists the obligations each one uses; the numbering follows the sections, and
the proof order must respect this column.

| Id | Title | Kind | Main source | Risk | Needs |
| --- | --- | --- | --- | --- | --- |
| O2-1 | Target constant $A_1^{(4)}$ | definition | Pas (9); BMR-I (1.7) | low | — |
| O2-2 | Enumeration of the order-5 1PI vertex | theorem | Srednicki ch. 58; BMR-I Fig. 2; AKN Fig. 2 | moderate (possibly higher: Lean decision cost at $N=5$) | O2-5 |
| O2-3 | Furry pair: the flavour-summed orientations cancel | theorem | Srednicki problem 58.2 | low–moderate | O2-2, O2-6 |
| O2-4 | Tadpoles vanish (connected/LSZ only) | theorem | — | low | O2-6 |
| O2-5 | Two-loop routing, loop bound $K\le2n_f+n_A+3$ | definition + theorems | CK-R (11)–(16) | moderate | — |
| O2-6 | Joint energy-first prescription and invariances | definition + theorems | REGULARIZATION.md section 4 | low–moderate | — |
| O2-7 | Integrability at fixed $\varepsilon$; $\exists!$ limit $\varepsilon\to0^+$ | $\exists!$ theorem | — (project) | high | O2-5, O2-6, O2-10, O2-12 |
| O2-8 | Nested equals joint for insertion classes | theorem | — | moderate–high | O2-7 |
| O2-9 | Embedding: the successor model at order $\le3$ is packet 6a; the joint prescription restricts to (D) | theorem | (Y₁); packet 6a | low–moderate | O2-5, O2-6 |
| O2-10 | Parametrization inside the energy integral; 2D and 6D formulas | theorem, infrastructure | CK-R (24)–(37); AKN (32)–(35) | moderate | O2-6 |
| O2-11 | Two-loop numerator algebra and the projection $P_2$ to $F_2$ | definition + theorems | CK-R rule 6; AKN (47)–(49), (64)–(65) | moderate | O2-10 |
| O2-12 | Positivity of $V$ on the simplex | theorem | CK-UV (4.3)–(4.7) | moderate–high | O2-10 |
| O2-13 | Counterterm insertion identities | theorem | CK-UV (3.24)–(3.28); CK-R (81)–(85) | low–moderate | O2-7 |
| O2-14 | Longitudinal $k^\mu k^\nu$ terms reach $F_1$ only | theorem | — (recalled) | low–moderate | O2-7 |
| O2-15 | One-loop Ward identity $\delta_1^{(2)}=\delta_2^{(2)}$ | theorem | (68.13); AKN (29)–(30) | moderate | O2-7 |
| O2-16 | $\delta_1^{(4)}$ feeds $F_1$ only | theorem | O-8 | trivial | O2-21 |
| O2-17 | UV cancellation per unit as $\Lambda\to\infty$ | theorem | CK-UV (2.11)–(3.40); AKN (70)–(79) | high | O2-10, O2-13, O2-15 |
| O2-18 | VP unit: spectral form, value $\frac{119}{36}-\frac{\pi^2}3$ | theorem | Srednicki (62.25); BMR-II (1.1)–(1.10) | moderate | O2-8, O2-13, O2-14 |
| O2-19 | Regulator-fermion decoupling $M_f\to\infty$ (derivative bound) | theorem | — | moderate | O2-18 |
| O2-20 | Covariance of the order-5 vertex, via the parametric form | theorem | CK-R (30)–(31) | moderate–high | O2-7, O2-10 |
| O2-21 | No $q^\mu$ term (mirror pairs or Ward identity); $\exists!$ form-factor pair at order 5 and per unit | $\exists!$ theorem | packet 2 | moderate–high | O2-11, O2-14, O2-20 |
| O2-22 | $q^2\to0^+$ limit of the order-5 $\hat F_2$ at fixed regulators, uniform over pairs; regulated $F_2^{(4)}(0)$ | $\exists!$ theorem, then definition | BMR-I (1.20), p. 834 c); BMR04 (117) | moderate | O2-12, O2-20, O2-21 |
| O2-23 | Infrared limit; per-unit expansions, log cancellation via O2-15 | theorem | BMR-I (1.20), p. 834–835, p. 852; AKN (85)–(95) | high | O2-15, O2-17, O2-18, O2-19, O2-22 |
| O2-24 | $\mathrm{Li}_2,\mathrm{Li}_3$ and their special values | infrastructure | BMR-I App. A | moderate | — |
| O2-25 | Exact limits of the units | theorem | BMR-I p. 852 (targets) | **highest** | O2-23, O2-24 |
| O2-26 | Assembly: $16\pi^4F_2^{(4)}(0)\to A_1^{(4)}$ | theorem | — | low | O2-1–O2-25 |

**Carriers needed for exact declarations** (none exists yet):

| Carrier or definition | Kind | Notes |
| --- | --- | --- |
| Successor of `VertexKind` with order-labelled counterterms, or a `Params` successor with graded coefficients $d_i^{(2)},d_i^{(4)}$ | meaning-carrying definition | section 8, question 2; packet 6a's objects must embed (O2-9, as (Y₁) did for packet 5) |
| Two-loop routing (two chords) and `lineMomentum₂` | definition | O2-5 |
| Two-loop energy-first integral on $(\mathbb R^4)^2$ | definition (generic operation) | O2-6; returns 0 off integrability, like (D), so statements assert integrability |
| Two-loop `contractionValue` and the order-graded 1PI function $V^{\mu,[5]}$ | source-facing definitions | sum over contractions of total order exactly 5 |
| Renormalized order-5 vertex: $d^{(2)}$ from (Z₆), (Z₉), (K₀) | definition | reuses frozen predicates; (Z₈) is now a premise |
| Projector $P_2$ | definition | O2-11; per-class $F_2[G]$ |
| Form factors at order 5 from O2-21 | $\exists!$, then definition | as packet 2 |
| Regulated $F_2^{(4)}(0;m_\gamma,\Lambda,M_1,M_2)$ from O2-22 | $\exists!$, then definition | with a characterization theorem |
| $\mathrm{Li}_2$, $\mathrm{Li}_3$, $\zeta(3)$ value | infrastructure | O2-24 |
| Headline | theorem | shape (b) of 5.6: $q^2\to0^+$ first at fixed regulators, then the joint regulator limit (D-5's order; proposed, pending the author's ruling); section 8, questions 3, 5, 6 |

As at one loop, Lean's integral and `limUnder` return junk values off their domains, so the
source-facing statements must assert integrability or use `Tendsto`-style conclusions.

## 8. Open design questions for the author

1. **Ward identity: theorem or condition?** Options: (a) prove
   $\delta_1^{(2)}=\delta_2^{(2)}$ at fixed regulators from (Z₅) and the charge condition
   (O2-15); (b) assume it, which would be a smuggled hypothesis and is not acceptable for a
   source-facing theorem; (c) compute $\delta_1^{(2)}$ and $\delta_2^{(2)}$ separately in closed
   form and use the values. **Recommendation: (a)**, which is cheap at one loop (an integrand
   identity plus differentiation under the integral) and reusable for higher orders; (c) is
   a cross-check.
2. **Counterterms at order $e^4$.** Options: (a) order-graded counterterm coefficients
   $\delta_i=e^2d_i^{(2)}+e^4d_i^{(4)}$ with separate vertex kinds of order 3/5 (`gaugeCt`)
   and 2/4 (`fermionCt`, `photonCt`), each condition imposed order by order; (b) a formal
   polynomial ring in $e$; (c) keep single reals and solve the truncated conditions exactly
   (rejected: spurious higher orders, section 2). **Recommendation: (a).** For the 1PI
   headline only $d_i^{(2)}$ matter, and $d_1^{(4)}$ is quantified over ("for every
   $d_1^{(4)}$", the analogue of D-32's treatment of $\delta_3$).
3. **The order of limits and the $M_f\to\infty$ limit.** In every option $q^2\to0^+$ comes
   first, at fixed regulators and uniformly over on-shell pairs (O2-22): a joint limit in
   $q^2$ and $m_\gamma$ does not exist at order $e^5$ (5.6). For the regulator limit that
   follows, the options are: (a) joint in $(m_\gamma,\Lambda,M_1,M_2)$, with $c_f$ determined
   by the Pauli–Villars conditions and no constraint on $M_2/M_1$; (b) iterated, $M_f\to\infty$
   last; (c) $M_f\to\infty$ first at fixed $\Lambda$. The derivative bound of O2-19, if it holds
   uniformly, makes (a) available. **Recommendation: (a)** for the regulator limit, with (b)
   as the fallback if uniformity in $\Lambda$ proves costly. Together this is D-5's iterated
   order ($\varepsilon$ first, then on shell, then $q^2$, then regulators). Proposed, pending
   the author's ruling.
4. **Two-loop prescription: joint or nested?** **Recommendation: joint** (all energies, then
   all spatial momenta). It is invariant under change of loop momenta (O2-6), its energy
   integral is elementary (section 4.3), and the frozen (D) is its one-loop case. Nested
   values are then theorems for the insertion classes (O2-8), where they are needed to
   reuse the frozen Σ and Π.
5. **Headline at order $e^5$: LSZ amplitude or 1PI vertex?** The LSZ form additionally needs
   the two-loop self-energy with on-shell conditions at order $e^4$ (fixing $d_2^{(4)},d_m^{(4)}$;
   otherwise the LSZ limit fails or has the wrong residue), the two-loop photon leg, and the
   order-$e^5$ charge condition. These order-$e^4$ data multiply the tree, so they should
   reach $F_1$ only (to be proved). But the LSZ amplitude also contains the one-loop photon
   leg times the one-loop vertex, an order-$e^5$ term $\Pi(q^2)\,F_2^{(2)}(q^2)$. It reaches
   $F_2$ at $q\ne0$ and vanishes as $q\to0$ only through (Z₈) or the background-field factor
   $q^2/(q^2+m_\gamma^2)$ of 5.3. It does not enter the 1PI vertex. **Recommendation:** the 1PI
   vertex (62.39) for the first milestone, stated with the on-shell order-$e^2$ data
   (Z₅), (Z₈), (K₀); the LSZ form and the Landé factors as a later packet with an equivalence
   theorem, as packet 6c did at one loop.
6. **Extraction of $A_1^{(4)}$.** Define $V^{\mu,[5]}$ as the sum over contractions of total
   order exactly 5 with $\delta_i^{(2)}=e^2d_i^{(2)}$. It is then $e^5$ times an
   $e$-independent matrix. Its Pauli form factor in the normalization of (63.18), which
   carries an overall factor $e$, is $e^4\hat F_2$, so $[e^4]F_2:=\hat F_2$ needs no limit
   in $e$. The headline then takes one of the two shapes of 5.6, with $q^2\to0^+$ first at
   fixed regulators: (a) for every $\eta>0$ there are $\delta,R$ such that for all regulators
   with $m_\gamma<\delta$ and $\Lambda,M_1,M_2>R$ and all admissible counterterms there is
   $q_0>0$ (depending on the regulators) such that, at every on-shell pair with
   $0<q^2<q_0$, every form-factor pair of $V^{\mu,[5]}$ has
   $|16\pi^4\hat F_2-A_1^{(4)}|<\eta$; or (b) the $\exists!$ theorem of O2-22, the
   regulated $F_2^{(4)}(0)$ it defines, and the regulator limit of that number.
   **Recommendation:** this graded form, in shape (b). A limit in $e$ is unnecessary, and the
   truncated model would make it artificial. The order of limits is proposed, pending the
   author's ruling. The one-loop pattern of (I)/(H), one $\delta$ for both $q^2$ and
   $m_\gamma$, cannot be used (5.6).

## 9. Source assessment

What each pinned source supplies, and its gaps:

- **BMR-I.** The setup: Feynman gauge, a photon mass (1.13), p. 832, and on-shell
  renormalization by subtraction at $t=0$, p. 829–830. The infrared structure (1.14)–(1.20),
  p. 833–835, with the per-graph infrared statements a)–c) on p. 834 (the ladder and crossed
  pair carries the whole fourth-order divergence at $t\ne0$; the evidence for 5.6).
  Per-graph $F_2^{(4)}(0)$, p. 852, and the totals, p. 853. Nielsen functions, Appendix A.
  *Gaps:* the method is dispersive, and there is **no Pauli–Villars regulator**: UV
  divergences are handled by renormalized subgraphs and subtracted dispersion relations.
  BMR write $p^2=-m^2$ and use $i\gamma$ notation (BMR-II (1.35)).
- **BMR-II.** Derivations per cut graph: the VP insertion (1.1)–(1.10), p. 868–869; the
  corners (1.11)–(1.14); the ladder and its non-commuting $\lambda\to0$ limit (1.15)–(1.33),
  p. 871–875; the cross graph from (1.75); the three-body cuts (2.1)–(2.72). *Gaps:* cut
  graphs are not Feynman graphs, and per-cut values carry $\ln^22$ and $\mathrm{Li}_4(1/2)$,
  which cancel in the sum. `pdftotext` extracts the equations badly; read the rendered
  pages.
- **CK-R.** Parametric Feynman–Dyson rules: $U$, $B_{ij}$, $V$ and the contraction rule
  (1)–(9); their derivation (10)–(37); the circuit formula (51); Nakanishi's identity
  (81)–(86); factorization of self-energy insertions (87)–(95). *Gaps:* Bjorken–Drell metric;
  the regularization is dimensional, (64)–(67), so route A must substitute its own; the
  worked example is sixth order (Sec. V).
- **CK-UV.** UV power counting (2.3)–(2.7); the $K$-operation (2.8)–(2.27); its relation to
  on-shell renormalization (3.32)–(3.43); IR power counting (4.1)–(4.34); IR factorization
  (5.1)–(5.15). *Gaps:* formal dimensional regularization (2.1), and infrared subtractions
  designed for numerics. Its own caution, p. 4005, that (5.14) may still contain logarithmic
  divergences, is left open there.
- **AHKN.** The Ward–Takahashi-summed form (4.29)–(4.31), the building blocks (4.20)–(4.46),
  the worked fourth-order example in §7.2, and residual renormalization (7.16). *Gaps:*
  misprints in §7.2 (below).
- **AKN.** The same fourth-order example, self-consistent: (55)–(59), (67)–(68), (70)–(71),
  (74)–(79), (85)–(98). It reproduces $\Delta M_{4a}$ (below). *Gaps:* the goal is numerical,
  and $\Lambda$, $\lambda$ are informal (p. 11).
- **Pet.** Karplus–Kroll graph IIc as auxiliary-variable integrals (2.1)–(2.4), p. 678–679;
  rigorous bounds; the total $\mu^{(4)}=(-0.39\pm0.11)\alpha^2/\pi^2$, (4.2), p. 682–683.
  *Gaps:* **this is not the exact result.** It is the bounds paper; its references 4) and 7)
  and a note added in proof point to the analytic evaluation (Helv. Phys. Acta, "in the
  press"). The exact paper is Helv. Phys. Acta 30 (1957) 407 (BMR-I footnote 2, p. 825).
- **BMR04.** An independent check in dimensional regularization; the $F_2^{(2l)}$ expansion
  (117), whose infrared pole $-q^2/\bigl(6(D-4)\bigr)$ at $q^2\ne0$ is the
  dimensional-regularization form of the logarithm of 5.6. Its per-graph values are specific
  to dimensional regularization.
- **Pas.** The closed form and the value (9). Background.

**Misprints in AHKN §7.2.** The rendered pp. 31–32 were checked, and each item was compared
with AKN. The independent review (2026-11-17) re-checked the rendered pages and confirmed
items 1, 2, 3, 5 and 6 with its own evidence, given after each item; it refuted item 4, which
is withdrawn.

1. **(7.5), prefactor.** AHKN prints $(-\tfrac14)^2\,2$; AKN (67) has $(-\alpha/4\pi)^2$
   with no factor 2. AHKN's own (4.31) at $n=2$ gives $(-\tfrac14)^2(n-1)!=\tfrac1{16}$. With
   $\tfrac1{16}$ the integral reproduces $0.218$; with the 2 it would be $0.437$.
   *Confirmed:* (4.31) at $n=2$ gives $\tfrac1{16}$, AKN (67) has no 2, and $\tfrac1{16}$
   reproduces $0.2183$.
2. **(7.6), $G$.** AHKN prints $G=z_1A_1+z_2A_2+z_2A_3$; AKN (57) has $G=\sum z_iA_i$.
   Evidence: AHKN (4.46) and (7.10), and the $1\leftrightarrow3$ symmetry of $M_{4a}$.
   *Confirmed:* the printed $G$ differs from $\sum z_iA_i$ by $(z_2-z_3)A_3\ne0$; with it,
   $V\le0$ on about $0.56\%$ of the simplex interior (minimum $-0.058$), so the integrand is
   not even integrable.
3. **(7.7), $N_0$ and the $z_2$ term of $Z_0$.** AHKN prints
   $N_0=8G(2A_1A_2A_3-\sum A_iA_j-\sum A_i)$ and the $z_2$ term
   $8z_2(-A_1+A_2-A_3-A_1A_2+A_1A_3-A_2A_3+2A_1A_2A_3)$. AKN (68) has
   $N_0=G[E_0+8(2-\sum A_i)]$, which differs by $+16G$, and
   $8z_2(1-A_1A_2+A_1A_3-A_2A_3+2A_1A_2A_3)$. As printed, $N_0+Z_0\to-16z_1-32z_2-16z_3\ne0$
   in the infrared corner $z_{1,2,3}\sim s$, where $V\sim s^2$. The integrand then behaves
   like $s^{-3}$ against the measure $s^2ds$, a log divergence, although AHKN p. 31 states
   that $M_{4a}$ needs no IR subtraction. With AKN's forms the leading terms cancel, as they
   do at one loop in (7.2). $N_1$ and $Z_1$ in (7.7) agree with AKN (68) after expansion.
   *Confirmed:* at $A_i\to1$, AKN's forms give $N_0+Z_0\to0$ and the printed ones
   $-16z_1-32z_2-16z_3$; correcting either alone still fails; numerically $-801,-908,-1078$
   on $16^4,24^4,32^4$ nodes.
4. **(7.7), $C_0$. Withdrawn.** AHKN prints $-8(C_{12}+C_{13}+C_{23})$ with $C_{ij}$ from
   (4.44), and AKN (68) has $-24z_az_b/U$. The draft's discrepancy (an integral of about
   $2.88$) came from using the unprimed $B_{ij}$ in (4.44), which gives
   $3(z_1z_2+z_1z_3+z_2z_3)/U$. AHKN (4.44) uses the primed $B'_{ij}=B_{ij}-\delta_{ij}U/z_j$
   (AHKN (4.12); also AKN (43)–(44)). With it $C_{12}=C_{13}=C_{23}=z_az_b/U$, so
   $-8\sum C_{ij}=-24z_az_b/U$, which is AKN's $C_0$ exactly (independent review).
5. **(7.9), $N_1$.** AHKN prints $N_1=8GB_{12}(2-A_3)$; AKN (71) has
   $8z_3A_3B_{12}(2-A_3)$. With the full $G$, the $K_{12}$ term behaves like $t^{-2}$ as
   $z_3,z_b\sim t\to0$ (measure $t\,dt$), a spurious log divergence. $z_3A_3=G_{G/S}$ is
   what the factorization (AKN (72), CK-UV (2.17)) requires. *Confirmed:* the power count
   $t^{-2}\cdot t\,dt$ as $z_3,z_b\to0$; numerically $-31.4,-33.6,-35.3$ on successive grids,
   growing logarithmically.
6. **(7.10), $A_i$.** AHKN prints $A_i=1-z_1B_{1i}-z_2B_{2i}-z_3B_{3i}$; AKN (70) says
   "the same form as (55)", which has $/U$. $A_i$ must be homogeneous of degree 0 (AHKN
   (4.20)), and AHKN's (7.6) has the $/U$. *Confirmed:* homogeneity requires the $/U$, AKN
   (70) refers back to (55), and without it the integral diverges numerically.

Numerical confirmation (section 10): with AKN (67), (68), (70), (71) the $K$-subtracted
crossing integral $\Delta M_{4a}$ evaluates to $0.22260,\,0.21925,\,0.21856,\,0.21840$ on
$24^4,40^4,64^4,96^4$ Gauss–Legendre nodes with endpoint clustering. Successive differences
shrink by about 4.5, which extrapolates to about $0.21835$, matching AHKN (7.17) and AKN
(96), $0.218\,347(32)$. The independent review reproduced $0.222603$ at $24^4$ with the
same clustering, and with stronger clustering obtained
$0.218420,\,0.218361,\,0.218339,\,0.218335$ on $48^4,64^4,96^4,128^4$ nodes. With AHKN
(7.5)–(7.10) as printed (only the factor 2 of (7.5) removed) the same quadrature does not
settle ($-108,-134,-155$ on $16^4,24^4,32^4$ nodes), as items 3 and 5 predict. Items 1–3, 5
and 6 have now had the independent check that the ledger rules require; recording them in
[ERRATA-AND-DEVIATIONS.md](ERRATA-AND-DEVIATIONS.md) is a separate step, not taken here.

**Still missing** for this phase: Petermann, Helv. Phys. Acta 30 (1957) 407, and
Sommerfield, Ann. Phys. 5 (1958) 26 (the exact parametric evaluations, needed for O2-25
option 1); Kinoshita 1990 (World Scientific), which would supply the parametric fourth-order
integrands with their subtraction terms in one place; and a source for the spectral form of
$\Pi_R$ in O2-18 (Källén–Sabry; not located yet). The Feynman-parameter form is Srednicki
(62.25), and the two agree numerically (section 10).

## 10. Numerical record

Scratch computations, run 2026-11-17 with mpmath 1.3.0 and numpy 2.5.3. They were not
committed; each can be replayed from the formulas given here.

| Check | Method | Result |
| --- | --- | --- |
| $A_1^{(4)}$, VP part, $q$-type part, sum | mpmath, 40 digits | sum minus $A_1^{(4)}$ $=0$; values in section 1 |
| BMR04 (117) constant equals $A_1^{(4)}$ | mpmath | difference $5\times10^{-41}$ |
| BMR-I p. 852 per-graph sum | mpmath, 30 digits | equals $A_1^{(4)}$ (difference $5\times10^{-31}$) |
| VP spectral double integral (O2-18) | mpmath quadrature, 40 digits | $=\frac{119}{36}-\frac{\pi^2}3$ (difference $10^{-40}$) |
| $\mathrm{Li}_2(\frac12)$, $\mathrm{Li}_3(\frac12)$ closed forms; $\int_0^1\ln x\ln(1+x)dx/x$ | mpmath | agree to 40 digits |
| 2D energy formula (4.3) | mpmath, $n=2,3$, $w=3-0.7i,\ -2-0.3i$, $A$ non-diagonal | agree to $\ge13$ digits |
| absolute 2D energy integral | mpmath | $628.30,\ 628.32,\ 628.32$ at $R=10,10^2,10^3$ |
| AKN (58)–(59) from the loop matrix | by hand | agree |
| $\Delta M_{4a}$ (AKN form), AHKN form | numpy tensor Gauss–Legendre on the 4-simplex | section 9 |
| Spectral form of $\Pi_{R}$ against Srednicki (62.25) (O2-18) | mpmath, 20 digits, $k^2=0.3,\ 5$ | ratio $1.000\ldots$ to 20 digits ($+4.91\times10^{-4}$, $+5.77\times10^{-3}$ at $e=m=1$) |
| Size of the $q^2\ne0$ infrared term (5.6) | arithmetic | $(q^2/6m^2)\ln(m/m_\gamma)=100/12\approx8.3$ at $q^2=\delta m^2/2$, $m_\gamma=me^{-100/\delta}$ |
| Independent review (2026-11-17; mpmath 1.3.0, numpy 2.5.3, sympy) | replay | reproduced every row above; BMR04 (117) exactly, the per-graph sum to $2\times10^{-46}$; VP double integral to $2\times10^{-31}$; the 2D formula to 20 digits; the absolute 2D integral $628.303,\ 628.318,\ 628.3185$ against $2\pi/\varepsilon^2$; AKN (58)–(59) and $\sum z_iA_i=$ AKN (35)'s $G$ symbolically; the AHKN items of section 9 |
