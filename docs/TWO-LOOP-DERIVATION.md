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
obligations, and the AHKN errata (section 9). Aligned with the author's follow-up rulings
D-37 (2026-11-17; section 8): the open design questions are now rulings, the counterterms
stay single real numbers with the order separation as obligation O2-27, and the
regulator-fermion masses are removed last. Section 11 records a numerical validation of the
units at finite regulators (2026-11-17): every unit reproduces BMR-I's per-graph value.
Notation and conventions are the project's ([CONVENTIONS.md](CONVENTIONS.md)):
mostly-plus metric, $e<0$, $q=p'-p$, $r=\alpha/\pi=e^2/4\pi^2$, a Pauli–Villars photon
of mass $\Lambda$, a photon mass $m_\gamma$, Pauli–Villars regulator fermions of masses
$M_1,M_2$ with closed-loop coefficients $c_1,c_2$ (D-22), and energy-first loop integrals
(D-5, M1).

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
   (D-19). At $K=5$ the counterterm `gaugeCt` occurs inside one-loop graphs. D-37.3 keeps
   each counterterm a single real number and truncates the expansion; graded coefficients
   were not adopted. If the conditions fixing $\delta_i$ are the frozen one-loop ones, they
   are linear in $\delta_i$ with a source proportional to $e^2$, so $\delta_i=e^2d_i$ with
   $d_i$ independent of $e$. If a condition were imposed on a function truncated at order 5
   (as an order-$e^5$ charge condition or the later LSZ form would need), $\delta_1$ would
   solve a rational, not a polynomial, equation in $e$ and the truncated vertex would carry
   spurious higher-order terms. Either way, separating the orders is a proof obligation
   (O2-27; section 8, ruling 3).
5. **Regulator fermions.** D-32 keeps $M_1,M_2$ fixed. At two loops they enter $F_2$
   through the VP insertion and must be removed by a limit $M_f\to\infty$ (D-36), taken
   last (D-37.4).

## 3. Stage 1 — Enumeration at order $e^5$

The object is the 1PI electron–electron–photon function (62.39) at total order exactly 5
(D-37.6; section 8, ruling 6), $n_f=n_A=1$.

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

Two counterterm vertices, or one counterterm with one gauge vertex, give only trees with
bridges. With single real counterterms and the frozen order labels (D-37.3), no counterterm
contraction of total order 5 is a tree: the tree `gaugeCt` vertex has order 3 and occurs
only at total order 3. So the order-5 1PI function has no counterterm proportional to
$\gamma^\mu$ alone, and the overall divergence of the two-loop vertex (5.2) is not subtracted
in it. At fixed regulators that part is finite; it is expected to reach $F_1$ only (O2-16),
which the 1PI headline does not constrain. An order-5 tree counterterm would be a new
vertex kind, which D-37.3 does not introduce. Order-$e^4$ information on
$\delta_2,\delta_m,\delta_3$ cannot appear in the 1PI vertex at order 5 either (their only
contraction has a bridge). It matters only for the later LSZ restatement (D-37.6; section 8,
ruling 6), where it must be handled within O2-27.

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
  of the nine contraction classes of 3.1 and the six of 3.2, each with coefficient one and
  the stated sign. This generalizes packet 5's classification and (Y₁). Theorem; finite
  combinatorics, moderate size (the review notes that the cost of deciding the
  classification in Lean at $N=5$ may push it higher). Source: Srednicki ch. 58 rules;
  BMR-I Fig. 2; AKN Fig. 2 (seven vertex diagrams).
  **Status (2026-11-18): proved under momentum conservation**
  (`QED/TwoLoop/Enumeration*.lean`, `RelabelInvariance*.lean`; method and inventory in
  [TWO-LOOP-ENUMERATION.md](TWO-LOOP-ENUMERATION.md)).
  `QED.TwoLoop.Enumeration.onePIFunction₂_five_sub_four`, at every `P` and all external data,
  writes the order-exactly-5 part as an explicit finite sum: the nine classes of five gauge
  vertices, each summed over the $5!$ relabellings of its representative and divided by $5!$,
  plus the listed 1PI contractions with one counterterm vertex, divided by $N!$ (kernel
  checks). Relabelling invariance `QED.TwoLoop.Relabel.contractionValue₂_relabel` assumes
  connected vertices (X₁₇) and external momenta summing to zero. For 1PI contractions,
  `contractionValue₂_relabel_of_isOnePI` assumes momentum conservation only, since 1PI gives
  connectedness and attached externals. Hence coefficient one per class with its sign,
  `QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq`, under momentum conservation
  `pOut 0 = pIn 0 + kIn 0`. That the conservation hypothesis cannot be dropped is argued (the
  routing is not conserved without it), not proved. The counterterm contractions are grouped
  likewise into seven classes with coefficient one (the six of 3.2, with the two δ₃ slot
  pairings counted separately), so under momentum conservation the order-5 vertex is the sum
  over 7 + 7 class representatives (`QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq_classes`,
  with the Furry pair cancelled; see TWO-LOOP-ENUMERATION.md, section 3). **O2-2 is proved**
  for the 1PI vertex at fixed parameters.
- **O2-3 (Furry pair).** The two flavour-summed orientations of the three-vertex loop cancel
  at fixed $\varepsilon$. Per-flavour values are not objects of the model: X₂₆ sums the
  flavours inside the integrand. Proof: charge conjugation, $C\gamma^\mu C^{-1}=-\gamma^{\mu T}$,
  turns one orientation's integrand into minus the other's with the loop momentum reflected
  and shifted, flavour by flavour, so the cancellation needs the reflection and shift
  invariance of the two-loop prescription (O2-6) on integrable data. Integrability needs the
  flavour sum: one flavour's triangle decays like $|\ell|^{-3}$, and with
  $\sum c_f=\sum c_fM_f^2=0$ the sum decays like $|\ell|^{-7}$ (power counting, section 4.1).
  Theorem; low–moderate risk. **Status (2026-11-18): proved**
  (`QED/TwoLoop/FurryPair.lean`, with `QED/Algebra/ChargeConjugation.lean`).
  `QED.TwoLoop.Furry.furry_pair` holds under momentum conservation `pOut 0 = pIn 0 + kIn 0`,
  at every parameter set (so at every fixed $\varepsilon$) and all external indices: the values
  of F₊ and F₋ sum to zero. The connectedness that the routing change needs comes from the
  kernel-checked 1PI property of the two representatives. The proof needs no integrability.
  The amplitudes are related pointwise, flavour by flavour, by $C=\gamma^0\gamma^2$, and the
  joint prescription respects the integer unimodular change and the negation for every
  integrand. Consequence: `onePIFunction₂_five_sub_four_eq_furry`, the seven classes L, X,
  C±, S±, VP plus the counterterm contractions. Numerical replay of the charge-conjugation
  identities: `python3 scripts/numerics/two_loop_crosschecks.py furry`.
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
  **Status (2026-11-18): (i)–(iii) proved** for the frozen routing `lineMomentum₂` (T₄).
  (i) `QED/TwoLoop/Routing.lean`. Uniqueness, `QED.TwoLoop.Routing.eq_lineMomentum₂_of_isConserved`,
  needs no connectedness and no condition on the external momenta. Conservation,
  `QED.TwoLoop.Routing.isConserved_lineMomentum₂`, assumes connected vertices (X₁₇) and
  external momenta summing to zero.
  (ii) `QED/TwoLoop/RoutingChange.lean`, `QED.TwoLoop.Relabel.LineCorr.exists_routing_change`.
  It applies to two contractions whose lines correspond under a bijection of the vertices, up
  to orientation, which is how the chords change under relabelling. Both must have connected
  vertices and equal loop counts, and their external momenta must match vertex by vertex and
  sum to zero. Then the pulled-back routing is `lineMomentum₂ C (M ℓ + a)` with `M` an integer
  matrix with `IsUnit M.det`.
  (iii) `QED/TwoLoop/LoopBoundTwo.lean`, `LoopBoundTwoExact.lean`. The bound
  `QED.TwoLoop.LoopBoundTwo.loopCount_le_two_of_order` holds for 1PI contractions of total
  order at most $K\le2n_f+n_A+3$. The exact formula
  `QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq`,
  $2L+2n_f+n_A=V_3+2$, assumes attached externals (X₁₆), connected vertices (X₁₇) and
  $N\ge1$.

### 4.3 The two-loop energy-first prescription

Write $\ell_s=(t_s,\vec v_s)$. Two prescriptions extend M1:

- **Joint:** $\displaystyle\int_{\mathbb R^6}d^3v_1\,d^3v_2\left(\int_{\mathbb R^2}dt_1\,dt_2\,
  f_\varepsilon\right)$, then $\varepsilon\to0^+$.
- **Nested:** `energyFirstIntegral` applied twice, $\int d^3v_2\int dt_2\int d^3v_1\int dt_1
  f_\varepsilon$.

D-37.5 adopts the joint prescription (section 8, ruling 5); nested values are theorems for
the insertion classes (O2-8).

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
  **Status (2026-11-18): proved.** The definition is the frozen `jointEnergyFirstIntegral`
  (T₉) of packet T1 (D-38). The invariances are in `QED/TwoLoop/JointIntegralInvariance.lean`:
  `QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_add` (real shifts),
  `jointEnergyFirstIntegral_comp_matrix` (integer `M` with `IsUnit M.det`, acting equally on
  energies and space), `jointEnergyFirstIntegral_comp_neg` and
  `jointEnergyFirstIntegral_comp_matrix_add`. They hold for every integrand, with no
  integrability hypothesis: on non-integrable data both sides are 0.
- **O2-7 (well-definedness).** For each class of 3.1–3.2, with $m,m_\gamma,\Lambda>0$,
  $M_f>m$, the Pauli–Villars conditions, on-shell positive-energy $p,p'$ and $q^2\ge0$:
  the inner energy integral and the outer spatial integral are integrable for every
  $\varepsilon>0$, and the value has a unique limit as $\varepsilon\to0^+$. This is the
  two-loop analogue of packet 1's (E). Theorem; **high** effort; the main analytic risk of
  stage 2.
  **Status (2026-11-18): proved at helper level, per class.** For every class L, X, C±, S±
  (`QED/TwoLoop/ClassIntegrable.lean`, `jointEnergyFirstIntegrable_open`) and VP
  (`ClassIntegrableVP.lean`, `jointEnergyFirstIntegrable_VP`, using the two Pauli–Villars
  conditions), at every $\varepsilon>0$ and with momentum conservation, both stages of the class
  value's joint integral at the frozen routing are integrable (T₉′), with no condition on the
  regulators. Route: the parametric bridge, the refined pointwise bound and the refined
  criterion. **The $\varepsilon\to0^+$ limit is also proved** for every class, entrywise
  (`QED/TwoLoop/ClassLimit.lean`, `tendsto_contractionValue₂_open`,
  `existsUnique_tendsto_contractionValue₂_open`; `ClassLimitVP.lean` for VP, which also needs
  $M_f\ge m$), for $m,m_\gamma,\Lambda>0$, on-shell $p,p'$ with $q^2\ge0$ and momentum
  conservation. The limit is the $\varepsilon=0$ parametric integral, whose integrand is
  integrable on the simplex. Domination uses O2-12 ($V\ge c>0$). The limit is stated through
  a numerator chosen to equal the class numerator; uniformity in small $q^2$ (O2-22) is not
  addressed.
  **The order-$e^5$ vertex.** The seven counterterm classes also have $\varepsilon\to0^+$ limits
  for every value of the counterterms (`QED/TwoLoop/CountertermLimit.lean`; the δ₁ classes use
  positive energies), via an auxiliary independent loop that turns a one-loop integrand into a
  two-loop one. Hence the order-$e^5$ vertex (HV₁) has a unique limit (HV₂) at fixed regulators,
  for $m,m_\gamma,\Lambda>0$, $M_f\ge m$ with the PV conditions, on-shell positive-energy $p,p'$
  and $q^2\ge0$ (`QED/TwoLoop/VertexLimit.lean`, `existsUnique_isVertexOrderFiveLimit`), and
  `exists_isVertexOrderFiveLimit_headline` is the existence clause of the headline (HV₃) in its
  exact shape, for every choice of counterterms.
- **O2-8 (nested equals joint, for insertions).** For the insertion classes S₊, S₋ and VP,
  the joint value equals the outer one-loop integral of the frozen inner one-loop function
  (Σ, Π at fixed $\varepsilon$, then $\varepsilon\to0^+$, as appropriate). This is needed to
  reuse the frozen self-energy and vacuum polarization. Theorem; moderate–high (exchange of
  limits in $\varepsilon$ for the subloop and the outer loop).
  **Status (2026-11-18): VP class, conditional** (`QED/TwoLoop/NestedVP*.lean`). Unconditional:
  the routing change to a nested routing and the factorization of the integrand into the open
  chain times the one-loop vacuum-polarization integrand. The equality with the iterated
  energy-first integral (`contractionValue₂_VP_eq_nested_energyFirst`) assumes two explicit
  hypotheses: the integrability of both joint stages (O2-7 for this class) and a Fubini condition
  in $(t_2,\vec v_1)$. The second needs a sharper bound on the packet-6b spatial integrand than
  the existing one. The $\varepsilon\to0^+$ step and the classes S± remain.
- **O2-9 (embedding).** The analogue of (Y₁) for the successor model (single real
  counterterms in `Params` with the frozen order labels, D-37.3; two-loop routing; the joint
  prescription, D-37.5; section 7 carriers): at total order $K\le 2n_f+n_A+1$ (the frozen
  source-facing bound, which includes the vertex at $K=3$) it reproduces packet 6a, that is
  the same contractions
  with the same values, the order-$e^2$ counterterm data and the frozen predicates (Z₅),
  (Z₈), (K₀); and the joint prescription of O2-6, applied to one-loop data, is the frozen
  (D). (Order at most 3 alone is not enough: two-loop 1PI contractions exist with no
  externals at order 2 and with one external photon at order 3.) Without it the two-loop
  statements would not be about the frozen model. Theorem;
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
  **Status (2026-11-18): proved for scalar propagators, at helper level.** These are not yet
  statements about the model's contraction values: numerators (O2-11), the Pauli–Villars-combined
  integrands and the link to `lineMomentum₂` remain.
  - 2D energy formula of 4.3: `QED.Integration.TwoLoop.integral_inv_neg_quadratic_add_pow`,
    with integrability (`QED/Integration/TwoLoopEnergyIntegral.lean`), for $A$ positive
    definite $2\times2$, $\operatorname{Im}w<0$, $n\ge2$.
  - General Feynman formula: `QED.Integration.Feynman.prod_inv_eq_factorial_mul_integral_simplex`
    (`FeynmanParameterGeneral.lean`), for factors in the open lower half plane.
  - 6D spatial formula, previously recalled: `QED.Integration.Spatial.integral_inv_quadForm_add_pow`
    (`SpatialIntegralSix.lean`), for $k\ge4$, $A$ positive definite, $w$ off the closed
    negative real axis.
  - Scalar parametric representation:
    `QED.Integration.TwoLoop.jointEnergyFirstIntegral_prod_inv_lineDenom`
    (`TwoLoopParametric*.lean`). It covers $N=m+1\ge5$ scalar propagators
    $k_i\cdot k_i+M_i^2-i\varepsilon$ with line momenta $\sum_s\alpha_{is}\ell_s+p_i$, at
    $\varepsilon>0$. It assumes spanning loop coefficients (two independent $\alpha_i$) and
    $U^{-2}$ integrable on the simplex. Both stages of the joint integral are then integrable,
    and the value is $-\pi^4(N-5)!\int_\Delta U^{-2}(V-i\varepsilon)^{4-N}$.
  - Integrability criterion (`SymanzikIntegrability.lean`,
    `SymanzikIntegrabilityParametric.lean`). `integrableOn_inv_sq_symanzikU_of_criterion`
    gives $U^{-2}$ integrable under the no-subdivergence criterion `NoSubdivergence α`:
    every line has at least three lines not parallel to it. The corollary
    `jointEnergyFirstIntegral_prod_inv_lineDenom_of_noSubdivergence` replaces the two
    hypotheses on $U$ by the criterion. For the energy step, `integral_prod_lineDenom_eq_of_span`
    needs only the spanning condition. The criterion is proved sufficient; its necessity is not
    proved, and the only evidence for it is a Monte Carlo check.
  - Classes (`SymanzikIntegrabilityClasses.lean`). The loop matrices `class5LoopMatrix c` are
    integer routings written for that file, not `lineMomentum₂`. That they are loop matrices
    of the class representatives is checked numerically only
    (`scripts/numerics/two_loop_positivity.py`). With one denominator per line, L, X, C±, F±
    satisfy the criterion and S±, VP do not (`noSubdivergence_loopMatrix`,
    `not_noSubdivergence_loopMatrix`). With each photon line doubled (`class5LoopMatrixPV`),
    every class but VP satisfies it. VP satisfies it once its bubble lines are doubled too
    (`loopMatrixVPBubble`).
  - **Link to the model (2026-11-18).** The frozen chord routing of every class equals its class
    routing up to an integer unimodular change of loop momenta, kernel-checked
    (`QED/TwoLoop/ParametricBridgeLX.lean`, `ParametricBridgeC.lean`, `ParametricBridgeS.lean`,
    `ParametricBridgeVP.lean`), so the "numerically only" caveat above is removed. Each class
    value is a joint integral of a degree-≤4 numerator over Pauli–Villars-form denominators
    (`parametricForm_open` for L, X, C±, S±, the photon pairs combined; `parametricForm_VP`).
    For VP the regulator-flavour sum is derived, not assumed: by the two PV conditions and the
    vanishing of odd γ-traces (the odd mass terms cancel only after the loop trace), it becomes
    four terms of bubble shapes (1,3), (2,2), (3,1), (2,2) (`ParametricBridgeVPFlavour.lean`,
    `flavourSum_bubble`); all four satisfy the criterion, but only the two (2,2) terms have the
    `loopMatrixVPBubble` shape.

  Numerical replay: `python3 scripts/numerics/two_loop_crosschecks.py energy2d`, `feynman`,
  `param`, `criterion`.
- **O2-11 (numerator algebra and projection to $F_2$).** The parametric numerator of each
  class: the loop momenta in the numerator replaced by contractions in the $B_{ij}$ and the
  powers of $V$ lowered accordingly (CK-R rule 6, (7), (37); AKN (64)–(65)); and a
  projector $P_2$, a linear map on the vertex value at on-shell $(p,p')$ that returns $F_2$
  whenever the value has the form (G₀). AKN (47)–(49) project the Ward–Takahashi-summed
  self-energy form at $q\to0$; at $q\ne0$ a trace projector on the spinor bases is the
  candidate (**recalled**). Per-class $F_2[G]$ (section 5.1) is defined through $P_2$, since
  a single class need not have the form (G₀) (O2-21). Definition and theorems; moderate.
  **Status (2026-11-18): parametric numerators, partial.** Degree ≤ 2 proved
  (`QED/Integration/TwoLoopParametricNumerator.lean`), with the integrability hypotheses replaced
  by the four-lines criterion `NoSubdivergenceQuadratic`
  (`QED/Integration/SymanzikIntegrabilityQuadratic.lean`; it holds for L, X, C± with doubled
  photons and for the VP bubble form, not for S±, VP, F±). Degree 4: fourth moments and the
  energy step proved (`TwoLoopMomentsQuartic.lean`, `TwoLoopNumeratorQuartic.lean`); the spatial
  step and the assembly are also proved (`TwoLoopNumeratorQuarticFull.lean`, N ≥ 7, under
  `tr²A·U⁻⁴` integrable or the five-lines criterion, which holds only for X with doubled photons).
  A refined criterion `NoSubdivergenceRefined` (`SymanzikIntegrabilityRefined*.lean`) gives the
  integrability of the weight $U^{-k}\prod_{e\in E}\sqrt{1+Q_e/U}$ and holds for L, X, C±, S± with
  doubled photons and the VP bubble form. The pointwise bound of the numerator integrand by that
  weight is proved (`QED/Integration/TwoLoopRefinedBound*.lean`, `RefinedBound`), which gives
  the degree-4 representation under the refined criterion for N ≥ 8 lines
  (`jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined`). Projection to $F_2$:
  see O2-21.
- **O2-12 (positivity of $V$).** On the closed simplex, for on-shell $p,p'$ with $q^2\ge0$
  and $m_\gamma>0$, $V$ is bounded below by a positive constant. This is the two-loop
  analogue of $D\ge(1-x_3)^2m^2+x_3m_\gamma^2$ ("no thresholds": a free electron cannot
  emit a massive photon). It gives the $\varepsilon\to0^+$ limit of O2-7 by dominated
  convergence. CK-UV (4.3)–(4.7), p. 3999, write $V$ on the electron path as
  $\sum z_i(1-A_i)$ plus photon-mass terms, with $A_i$ a current fraction. Theorem;
  **moderate–high risk**: a uniform lower bound, including at faces where $U\to0$, is
  unproved and has not been located in a pinned source. O2-22 needs it uniformly for small
  $q^2\ge0$. **Status:** numerically positive for all nine classes, with minimum
  $m_\gamma^2(1-m_\gamma^2/4m^2)$ approached along edges where $U\to0$, and nondecreasing in $q^2$
  (`scripts/numerics/two_loop_positivity.py`);
  **proved for L and X, at helper level** (`QED/Integration/SymanzikPositivity.lean`,
  current-fraction form of CK-UV). The statements are
  `QED.Integration.TwoLoop.le_symanzikV_classL` ($V\ge m^2E^2+m_\gamma^2(1-E)$),
  `le_symanzikV_classX` ($V\ge m^2E^2/4+m_\gamma^2(1-E)$), with $E$ the electron-line weight,
  and the uniform forms `symanzikV_classL_ge`, `symanzikV_classX_ge`, `symanzikV_classL_pos`,
  `symanzikV_classX_pos` (the last two for $m,m_\gamma\ne0$). They hold for the per-class
  loop matrices `loopMatrixL`, `loopMatrixX` (that is, `class5LoopMatrix .L`, `.X`; see O2-10
  on how these were matched to the representatives) and the line momenta `classLXMomenta`.
  They assume photon masses
  $\lambda_i^2\ge m_\gamma^2$, on-shell $p\cdot p=p'\cdot p'=-m^2$ and $q\cdot q\ge0$, and
  hold at every point of the simplex with $U(z)\ne0$. The hypothesis $U\ne0$ is needed because
  `symanzikV` takes a junk value at $U=0$. **The other classes** C±, S±, VP (F± cancel, O2-3)
  are proved in the same way, with the same hypotheses, and also the Pauli–Villars forms of all
  seven classes and the doubled-bubble VP form, using a general lemma that repeating a line with
  a mass at least the original's preserves a lower bound
  (`QED/Integration/SymanzikPositivityClasses.lean`: `le_symanzikV_classCp`, `…Cm`, `…Sp`,
  `…Sm`, `…VP`, their `_ge` and `_pos` forms, `symanzikV_class*PV_ge`,
  `symanzikV_VPBubble_ge`, `le_symanzikV_comp_of`); same caveat on the loop matrices. The use
  of the bound in the $\varepsilon\to0^+$ limit (O2-7, O2-22) remains.

## 5. Stage 3 — Subtraction at fixed regulators

Everything in this stage happens at fixed $m_\gamma,\Lambda,M_f$ and after
$\varepsilon\to0^+$, where every class is finite. "Subtraction" means grouping each
divergent subgraph with its counterterm insertion and proving identities between finite
quantities. It does not mean defining new objects by subtraction.

### 5.1 Counterterm insertion identities

Write $\delta_i=e^2d_i$, with $d_i$ the order-$e^2$ coefficients fixed by (Z₆),
(Z₉) and the charge condition (K₀) (or its LSZ form (L₄)). The counterterms are single real
numbers (D-37.3); that they have this form, and that the coefficient below is what the
truncated vertex delivers, is obligation O2-27. The vertex factor of
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
- **O2-15 (the Ward identity at one loop).** At fixed $m_\gamma,\Lambda$: if $e\ne0$, the electron is
  on shell (Z₅) and the charge condition (K₀) holds, then $\delta_1^{(2)}=\delta_2^{(2)}$. (The premise
  $e\ne0$ is needed: at $e=0$ every $Z_1$ satisfies (K₀) while $\delta_2=0$.) **Proved**
  (`QED/TwoLoop/WardIdentity.lean`), on the $\varepsilon=0$ parametric closed forms, separately
  for each Pauli–Villars term; the proof uses those closed forms only. The original plan was a
  different route: the differential identity
  $\partial\tilde S/\partial p_\mu=-\tilde S\gamma^\mu\tilde S$, differentiation under the
  one-loop integral, and the relation of the $q\to0$ vertex to $\partial\Sigma/\partial p$.
  At $\varepsilon>0$ that identity has an $O(\varepsilon)$
  defect, since $\tilde S_\varepsilon^{-1}=(\not p+m)(p^2+m^2-i\varepsilon)/(p^2+m^2)$ is not
  affine in $p$, so that route would work only in the $\varepsilon\to0^+$ limit. Only the
  photon line is regulated, and the identity holds line by line on electron lines, so the
  Pauli–Villars photon preserves it (REGULARIZATION.md, route B row). Theorem; moderate.
  Source: Srednicki (68.13) (statement); AKN (29)–(30) and AHKN (4.29)–(4.30) (the
  Ward–Takahashi identity used to sum vertex graphs); BMR04 section 4 ("$Z_2^{(1l)}=-Z_1^{(1l)}$
  due to the Ward identity", their sign convention). Ruling: proved, not imposed (D-37.2;
  section 8, ruling 2).

With O2-15, the $\delta$-terms reduce to $d_1F_2^{(2)}+(d_2-d_m)F_2^*-d_3F_2^{(\gamma)}$.

- **O2-27 (order separation for single real counterterms; added for D-37.3).** The
  counterterms are the single real numbers $\delta_1,\delta_2,\delta_m,\delta_3$ of `Params`,
  fixed at fixed regulators by the frozen conditions (Z₆), (Z₉) and (K₀), and the expansion is
  truncated: $V^{\mu,[5]}$ is the sum over contractions of total order exactly 5, with the same
  $\delta_i$ as at order 3. Prove:
  1. **Homogeneity.** The frozen conditions concern one-loop functions ((Z₄), (Z₇) and the
     order-$\le3$ vertex). They are linear in the $\delta_i$, with sources proportional to
     $e^2$ (for (K₀): $e\delta_1\gamma^\mu+e^3\Lambda^\mu(p,p)=0$ between on-shell spinors).
     With the uniqueness in (Z₆), (Z₉) and that of the charge condition, $\delta_i=e^2d_i$
     with $d_i$ independent of $e$ at fixed regulators.
  2. **Extraction.** Consequently $V^{\mu,[5]}=e^5W^\mu$ with $W^\mu$ independent of $e$, and
     its Pauli form factor in the normalization of (63.18), which carries an overall $e$, is
     $e^4\hat F_2$. So $[e^4]F_2:=\hat F_2$ is a coefficient, exactly the order-$e^4$ quantity
     of 5.1–5.6 with $d_i$ in place of the counterterms, and no limit in $e$ is needed.
  3. **If a condition is truncated at order 5.** An order-$e^5$ charge condition, or the
     on-shell conditions the later LSZ restatement needs (D-37.6), would make $\delta_i$ a
     rational function of $e^2$ with $\delta_i=e^2d_i+O(e^4)$, and the truncated vertex would
     carry spurious terms of order $e^7$ and beyond. Then $[e^4]F_2$ must be defined either as
     a Taylor coefficient at $e=0$ of the truncated Pauli coefficient (after proving its
     regularity in $e$) or as the limit $e\to0$ of its order-$e^4$ remainder quotient at fixed
     regulators, and shown to equal that quantity.

  Items 1–2 are the cleaner route and suffice for the 1PI headline; item 3 is needed only if
  the successor model imposes a condition on an order-5 function. Which conditions it imposes
  is a choice to be settled, with the author and the reviewers, when the declarations are
  drafted. Theorem; low for items 1–2 (linear algebra on the frozen existence and uniqueness
  theorems), moderate for item 3.
  **Status (2026-11-18): items 1–2 proved for the vertex function; item 3 not addressed**
  (`QED/TwoLoop/CountertermScaling.lean`). The standing hypotheses are $m,m_\gamma,\Lambda>0$,
  $M_1,M_2>m$, the two Pauli–Villars conditions and $e\ne0$.
  - Item 1: `QED.TwoLoop.Scaling.counterterms_eq_sq_mul`. If the counterterms of `P` satisfy
    (Z₅), (Z₈) and (K₀) at charge $e$, and $d_1,d_2,d_m,d_3$ satisfy the same conditions at
    charge 1, then $\delta_i=e^2d_i$ for each $i$. Conversely, $e^2$ times admissible
    counterterms at charge 1 is admissible at charge $e$ (`isElectronOnShell_scale`,
    `isPhotonOnShell_scale`, `isChargeNormalized_scale`).
  - Item 2, for the vertex function: `QED.TwoLoop.Scaling.onePIFunction₂_succ_sub`. With
    $\delta_i=e^2d_i$, the part of total order exactly $K+1$ is $e^{K+1}$ times its value at
    $e=1$. `onePIFunction₂_five_sub_four_of_conditions` states this at order 5 under the
    frozen conditions.

  The statement about the Pauli form factor in item 2 needs the order-5 form factors (O2-21).

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

The overall divergence of the two-loop vertex is proportional to $\gamma^\mu$, so it does not
reach $F_2$ (CK-UV p. 3995: the overall degree; AKN p. 17: "it does not suffer from an
overall divergence ... dropped when the anomalous magnetic moment contribution is projected
out"). With single real counterterms (D-37.3) no order-5 tree counterterm absorbs it (3.2);
at fixed regulators it is a finite part of $F_1$, which may grow as $\Lambda\to\infty$.

- **O2-16 (the overall divergence and $F_1$).** The part of the order-5 1PI function that
  carries the overall divergence of each unit contributes to $F_1$ only, so the Pauli
  coefficient needs no order-5 tree counterterm. In route A this is the statement that the
  $\Lambda$-growth of each unit sits in its $\gamma^\mu$ component (the analogue of O-8, now
  without a counterterm to cite). Theorem; low, part of O2-17.
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
  Partial fractions in $k^2$ give the finite-regulator value exactly in terms of the
  one-loop $F_2$ of a massive photon and its mass derivative (section 11.6, item 4).
  Theorem; moderate. Its limit for the electron flavour is
  $$\int_0^1dv\,\frac{v^2(1-v^2/3)}{1-v^2}\int_0^1dx\,\frac{x^2(1-x)}{x^2+(1-x)\,\frac{4}{1-v^2}}
  =\frac{119}{36}-\frac{\pi^2}{3}$$
  (numerics: 40 digits). The inner integral is the one-loop $F_2/r$ with photon mass
  $\lambda$, $\lambda^2/m^2=4/(1-v^2)$; it is the same function as $C_1$ in
  REGULARIZATION.md section 6. BMR-II (1.1)–(1.10), p. 868–869, derives the same value
  dispersively (source). The exact evaluation needs only $\zeta(2)$. **Proved**
  (`QED/TwoLoop/VacuumPolarizationUnit.lean`): the evaluation of the explicit double integral
  above, $=\frac{119}{36}-\frac{\pi^2}3$ (`QED.TwoLoop.VPUnit.integral_vpUnit`), and the
  spectral identity for $M\ne0$, $k^2>-4M^2$
  (`QED.TwoLoop.VPUnit.integral_mul_log_eq_spectral`). That this double integral is the limit
  of the model's VP unit is not proved; it remains O2-8, O2-10 and O2-13.
- **O2-19 (regulator-fermion decoupling).** By D-37.4 the masses $M_1,M_2$ are removed
  last, after $q^2\to0^+$ and after $m_\gamma\to0$, $\Lambda\to\infty$ at fixed $M_f$. So the
  object is the already-limited VP-unit contribution of one flavour of squared mass $\mu$,
  $g(\mu)=\lim_{m_\gamma\to0,\,\Lambda\to\infty}g(\mu;m_\gamma,\Lambda)$, which exists by
  O2-18 (at $m_\gamma=0$, $\Lambda=\infty$ it is the superposition of one-loop vertices with
  photon masses $2\sqrt\mu/\sqrt{1-v^2}$). The flavours $f=1,2$ contribute
  $c_1g(M_1^2)+c_2g(M_2^2)$. No uniformity in $m_\gamma$ or $\Lambda$ is needed.
  A bound on $|g|$ alone does not suffice: $M_1=M_2$ is impossible when
  $M_f>m$ (the two Pauli–Villars conditions would force $M_f=m$), and $c_1,c_2$ blow up as
  $M_2\to M_1$. Solving the conditions,
  $c_1=(M_2^2-m^2)/(M_1^2-M_2^2)$ and $c_2=(M_1^2-m^2)/(M_2^2-M_1^2)$, so with
  $h(\mu)=g(\mu)/(\mu-m^2)$
  $$c_1g(M_1^2)+c_2g(M_2^2)=(M_1^2-m^2)(M_2^2-m^2)\,h[M_1^2,M_2^2]
  =(M_1^2-m^2)(M_2^2-m^2)\int_0^1h'\bigl(M_2^2+\theta(M_1^2-M_2^2)\bigr)\,d\theta ,$$
  a divided difference. The obligation is therefore a **derivative bound** on the limited
  function, for example $|h'(\mu)|\lesssim m^2\mu^{-3}\ln(\mu/m^2)$ for $\mu$ beyond a
  threshold (it follows from $|g|\lesssim(m^2/\mu)\ln(\mu/m^2)$ together with
  $|g'|\lesssim(m^2/\mu^2)\ln(\mu/m^2)$), which makes the contribution tend to $0$ as
  $\min M_f\to\infty$ with no constraint on $M_2/M_1$. Because $g$ is a one-variable
  function given by an explicit double integral (O2-18), the bound can be proved on that
  integral directly. (A heavy lepton of mass $M$ contributes about $\tfrac1{45}(m/M)^2$ to
  $A_2^{(4)}$; **recalled**, consistent with Pas.) One more point: the $m_\gamma\to0$,
  $\Lambda\to\infty$ limit of the whole regulated $F_2^{(4)}(0)$ at fixed $M_f$ (O2-23) must
  split as the $M_f$-independent units plus $c_1g(M_1^2)+c_2g(M_2^2)$, so that $M_f$ enters
  the inner limit only through the VP unit. Theorem; moderate, lower than under a joint limit.
  **Proved at helper level** for the explicit finite-regulator VP value of the numerical
  model (`QED/TwoLoop/VacuumPolarizationUnitLimit.lean`, electron mass $m=1$), not for the
  model's VP unit (that identification is O2-8, O2-10, O2-13). The $(m_\gamma,\Lambda)$-limit of
  the explicit value exists at fixed $M_1,M_2\ne0$, as a joint limit
  (`QED.TwoLoop.VPUnit.tendsto_vpUnitReg`). Pointwise in the parameters the Pauli–Villars sum
  is a second divided difference, which bounds this limited explicit value:
  $|\cdot-(119/36-\pi^2/3)|\le(M_1^{-2}+M_2^{-2})/45$ for $M_1,M_2\ge m$, with no constraint
  on $M_2/M_1$ (`QED.TwoLoop.VPUnit.abs_vpLimSum_sub_le`; the limit $M_1,M_2\to\infty$ is
  `tendsto_vpLimSum`, the D-37.4 order `vpUnitReg_iterated_limit`). No derivative bound is
  needed.

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
  **Status (2026-11-18): projectors proved** (`QED/Algebra/FormFactorProjector.lean`): for
  $e,m\ne0$, on-shell $p,p'$ and $q^2>0$, explicit trace functionals `formFactorProj₁`,
  `formFactorProj₂` recover every form-factor pair (`eq_formFactorProj_of_isFormFactorPair`), and a
  vertex whose on-shell sandwich has the four-term form $a\gamma^\mu+bK^\mu+cq^\mu+dS^{\mu\nu}q_\nu$
  has a form-factor pair iff $c=0$ (`exists_isFormFactorPair_iff`). **Algebraic halves of O2-20
  and O2-21 proved** (`QED/Algebra/SandwichReduction*.lean`, `QED/TwoLoop/VertexCovariance.lean`):
  a vertex covariant under the Lorentz maps fixing $p,p'$ (`IsLittleGroupCovariant`) has the
  on-shell sandwich form; a covariant vertex that also satisfies the mirror identity
  (`IsMirrorSymmetric`: charge conjugation followed by the reflection in $p+p'$) has exactly one
  form-factor pair; both properties pass to finite sums and integrals. Hence the second clause
  of the headline (HV₃) holds given covariance and the mirror identity of the order-5 limit
  (`existsUnique_isFormFactorPair_headline`). **Covariance of the limit is proved**
  (`QED/TwoLoop/LimitCovariance*.lean`, `isLittleGroupCovariant_headline`): on the parametric limit
  formulas, via the chain form of the open-line numerators, the VP loop trace, the counterterm
  limits and the invariance of the parametric integrand under Lorentz maps fixing $p,p'$. Open
  before that: proving these two properties for the limit (numerator covariance of the class amplitudes, invariance of the parametric integrand,
  and the C±, S± mirror pairing). **Mirror identity, partial** (`QED/TwoLoop/LimitMirror*.lean`):
  charge conjugation pairs C₊↔C₋, S₊↔S₋ and maps L, X, VP to themselves at fixed $\varepsilon$,
  between the data $(p',p)$ and $(-p,-p')$; the mirror identity of the vertex limit is reduced
  (`isMirrorSymmetric_headline_of_cov`) to the covariance of the seven class limits under the
  reflection in $p+p'$ (which reverses time, so it is applied to the limits, not at fixed
  $\varepsilon$) and the mirror identity of the counterterm part. The counterterm part is done up
  to the same kind of input (`QED/TwoLoop/CountertermMirror*.lean`): the δ₁ classes are mirror
  symmetric unconditionally, from the closed form of the one-loop vertex; the δ₂/δm and δ₃ classes
  pair by charge conjugation at fixed $\varepsilon$ and need the reflection covariance of two
  counterterm-class limits (`isMirrorSymmetric_headline_of_cov_ct`). **The reflection covariance
  of the nine limits is proved** (`QED/TwoLoop/ReflCovariance*.lean`, for every Lorentz map with a
  spinor lift, proper or not), so the mirror identity of the order-5 limit holds under the
  headline hypotheses, and **the form-factor clause of the headline is proved at fixed
  regulators**: for $e\ne0$, $m,m_\gamma,\Lambda>0$, $M_f>m$ with the PV conditions, any
  counterterms, on-shell positive-energy $p,p'$ with $q^2>0$, the limit of the order-5 vertex
  has exactly one form-factor pair (`QED/TwoLoop/FormFactorClause.lean`,
  `existsUnique_isFormFactorPair_headline`). O2-20 and O2-21 are proved for the vertex limit.
- **O2-22 ($q^2\to0^+$ at fixed regulators).** At fixed $m_\gamma>0$, $\Lambda$, $M_1,M_2$
  and the on-shell order-$e^2$ counterterms, the Pauli coefficient $\hat F_2$ of the order-5
  vertex (O2-27; D-37.6) has a limit as $q^2\to0^+$, uniformly over the on-shell
  pairs: there is
  exactly one number $a$ such that for every $\eta>0$ there is $q_0>0$ with
  $|\hat F_2-a|<\eta$ for every pair with $0<q^2<q_0$. By O2-20, $\hat F_2$ depends on the
  pair only through $q^2$, so uniformity reduces to a one-variable limit. The proof is
  continuity of the parametric representation at $q=0$ with $m_\gamma>0$, by dominated
  convergence, using O2-12 uniformly for small $q^2$. The number $a$ defines the regulated
  coefficient $F_2^{(4)}(0;m_\gamma,\Lambda,M_1,M_2)$, with a characterization theorem.
  $\exists!$ theorem, then definition; moderate. It is needed because the regulator limits
  are taken after $q^2\to0^+$ (D-37.1; 5.6). The headline is in quantifier form and does not
  mention this number, but the proof passes through it, and later phases can reuse it.

### 5.5 Infrared structure

At fixed $m_\gamma>0$ every unit is finite. As $m_\gamma\to0$:

- **Power-like divergences** ($\propto m/m_\gamma$) are expected by power counting where a
  mass insertion ($\tilde S^2$) sits on a line adjacent to an on-shell external line. AKN
  (85)–(86), p. 20, and AHKN section 6 (R-subtraction) remove such a divergence from the
  integrand of the Ward-summed self-energy form, and CK-UV (4.21) with the text after it
  (p. 4001–4002) gives the power counting. In the route-A units, after the projection to
  $F_2$ at $q	o0$, **none is seen** (numerics, section 11.4). The mass-insertion graph tends
  to a finite limit, and the bare S graphs show no $1/m_\gamma$ growth. So no power-like
  cancellation inside S is needed for $F_2$. The infrared logarithm of S comes from that of
  $\delta_2$. (Earlier versions of this bullet asserted a linear divergence that cancels via
  $\Sigma(-m)=0$; the numerics do not support it for $F_2$.)
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
  **Status (2026-11-18): proved at fixed regulators, helper level**
  (`QED/TwoLoop/PauliZeroLimit*.lean`, `existsUnique_isUniformPauliLimit`, `pauliZeroLimit`): for
  $m,m_\gamma,\Lambda>0$, $M_f\ge m$ with the PV conditions and any counterterms, the Pauli component
  of the order-5 vertex limit has a unique limit as $q^2\to0^+$, uniform over on-shell
  positive-energy pairs; the $1/q^2$ of the projector cancels at zeroth order pointwise and at
  first order by the evenness of the total numerator under the reflection fixing $p$, and the
  second-order coefficient converges by dominated convergence. The explicit Feynman-parameter
  form is surfaced (`QED/TwoLoop/PauliZeroExplicit*.lean`, `pauliZeroLimit_eq_sum`), the
  charge scaling gives the regulated $F_2^{(4)}(0;m_\gamma,\Lambda,M_1,M_2)$ = `pauliZeroFour`
  (a function of the regulators alone under the frozen counterterm conditions), and it is the
  sum of five unit functions VP, S, C, L, X (`QED/TwoLoop/UnitsRegulated.lean`,
  `pauliZeroFour_eq_sum_units`). The regulator limits of these units (O2-17, O2-19, O2-23) and
  their link to the representations of `docs/TWO-LOOP-UNITS.md` remain.
  **VP unit, partial link** (`QED/TwoLoop/UnitVPLink.lean`, at $m=1$): with (Z₈), the outer
  one-loop form `vpOuterF2` of the VP insertion equals the explicit `vpUnitReg` up to the
  normalization $16\pi^4$, via the spectral form of the model's $\Pi$ and Fubini; hence, given
  `VPUnitNested` (that the model's VP unit equals this outer form, still open: O2-8/O2-10/O2-13
  at $q\to0$), the VP unit tends to $\frac{119}{36}-\frac{\pi^2}3$ in the D-37.4 order.
  The δ₃ half of `VPUnitNested` is proved (`QED/TwoLoop/VPUnitNested*.lean`, `unit_d3Zero`, for
  every δ₃: the longitudinal part of the insertion vanishes exactly on shell, partial fractions
  with four distinct photon masses reduce the class to the frozen one-loop vertex, and continuity
  in the masses closes it), and `VPUnitNested` is equivalent to the bubble identity `VPHalf`
  (`vpUnitNested_iff_vpHalf`), which remains (O2-8 at the $\varepsilon\to0$ level). Partial progress
  (`QED/TwoLoop/VPHalf*.lean`): `VPHalf` is equivalent to a subtracted statement `VPHalfSub` with
  the $\Pi_{\rm loop}(0)$ part discharged; the five-mass partial fractions and the per-spectral-mass
  one-loop limit (distinct masses) are proved. Numerically the fixed-$\varepsilon$ energy-first
  vacuum polarization is transverse up to an extra term $\varepsilon g^{\sigma\tau}S_\varepsilon(k)$
  (`scripts/numerics/vp_half/`), which must be shown to vanish in the limit. `VPHalfSub` (hence `VPHalf` and
  `VPUnitNested`) now follows from the fixed-momentum statement `VPHalfSubAt` along the boost curve
  (`QED/TwoLoop/VPHalfSub.lean`, `vpHalfSub_of_eventually`; the $q\to0$ step on the explicit side
  is proved), and `VPHalfSubAt` is equivalent to an outer one-loop form with $\Pi_{\rm loop}$
  inserted (`vpHalfSubAt_iff_outer`). That fixed-$q$ identity, O2-8 at the $\varepsilon\to0$ level,
  remains. Progress on the nested route: the Fubini condition `hG` is proved, so nested = joint
  for the VP class holds unconditionally at fixed $\varepsilon>0$
  (`QED/TwoLoop/NestedVPFubiniBound*.lean`, `contractionValue₂_VP_eq_nested`); the fixed-$\varepsilon$
  inner vacuum polarization is proved in closed form, transverse complex-mass part plus an explicit
  $\varepsilon g^{\mu\nu}S_\varepsilon(k^2)$ term (`QED/TwoLoop/VPHalfAt*.lean`); and the class value
  equals the outer integral of that closed form. Remaining: the $\varepsilon\to0$ limit of the outer
  integral (line-dependent prescriptions after the $x$-integration, and the $\varepsilon g S$ term,
  which absolute bounds cannot remove). The $\varepsilon\to0$ engine is proved
  (`QED/TwoLoop/VPHalfAtLimit*.lean`): for the one-loop vertex integrand with an extra photon power
  and arbitrary separate prescriptions on every line, the energy-first integral has a limit that
  does not depend on how the prescriptions vanish, continuous in the photon masses (via Feynman
  parameters, which merge the prescriptions); its value is identified with the frozen one-loop
  kernels, including the repeated photon pair. **The VP unit link is closed**
  (`QED/TwoLoop/VPHalfAtAssembly*.lean`, `vpHalfSubAt_of`; `QED/TwoLoop/UnitVPClose.lean`): the
  fixed-momentum identity holds at every on-shell pair with $q^2>0$, hence `VPHalfSub`, `VPHalf` and
  `VPUnitNested` hold unconditionally, and $16\pi^4$ times the model's VP unit tends to
  $\frac{119}{36}-\frac{\pi^2}3$ in the D-37.4 order (`unitF2_VP_iterated_limit_closed`, at $m=1$).
  The statements above that call `VPHalfSubAt` open are superseded by this.
  **L unit, partial link** (`QED/TwoLoop/UnitLLink*.lean`): the counterterm half is exact (δ₁
  from the frozen charge condition equals the doc's formula, and its unit contribution is
  $\delta_1(F_2^{(2)}(m_\gamma)-F_2^{(2)}(\Lambda))$); the $x$-integration of the $\lambda=0$
  integrand gives the kernel $K_{\rm L}$; and the $\lambda\to0$ limit of the doc's (3.4) is
  $\frac{11}{48}+\frac{\pi^2}{18}$, unconditionally (`QED/TwoLoop/UnitLLinkDominated.lean`,
  `tendsto_ladderRep`, with a proved uniform bound on the remainder). The
  graph half of the link (the two-loop Dirac and Gaussian-moment algebra, Cheng–Wu) and the
  $\Lambda\to\infty$ stage remain. Infrastructure for the graph half is proved
  (`QED/TwoLoop/ParamNumEval*.lean`: linearity and Wick's rule for the parametric numerator of
  electron chains, and a second-order jet calculus for `secondCoeff`; `UnitLGraph.lean`: the
  ladder's projected numerator as an explicit sum of chain traces). **The pointwise identity is
  proved** (`QED/TwoLoop/UnitLGraphTrace*.lean`: the Dirac traces in the planar subalgebra and the
  $u^2$ coefficients by jets; `openZero_L_eq` writes the ladder's class value as a simplex integral
  of explicit rational functions of the Feynman parameters). **The graph half now reaches the
  doc's (3.1)** (`QED/TwoLoop/UnitLGraphReduce*.lean`,
  `sixteen_pi_pow_four_mul_graphHalf_eq_doc_iterated`, at $m=e=1$, $0<m_\gamma<\Lambda$, with the
  outer-photon terms at mass $\Lambda$ kept), via general simplex merging, Pauli–Villars split and
  Cheng–Wu lemmas (`QED/Integration/SimplexMerge*.lean`, `ChengWu*.lean`). **The L unit link is
  closed** (`QED/TwoLoop/UnitLClose*.lean`, `unitF2_L_limit`, at $m=1$): with $\delta_1$ from the
  frozen charge condition, $16\pi^4$ times the model's L unit tends to $\frac{11}{48}+\frac{\zeta(2)}3$
  jointly as $m_\gamma\to0^+$, $\Lambda\to\infty$, via the $a$-integration (inner Pauli–Villars
  terms kept together), bounds uniform in $\lambda$, and the cancellation of $\ln M_\Lambda$ and
  $\ln\lambda$ against the counterterm. Earlier step (`QED/TwoLoop/PauliZero*.lean`): The Pauli
  projection of the order-5 vertex limit depends on the on-shell pair only through $q^2$
  (covariance under Lorentz maps that move $p,p'$, reached by two reflections), so the uniform
  statement is equivalent to a one-variable limit of `pauliAt` as $q^2\to0^+$
  (`uniform_iff_tendsto_pauliAt`). That limit is open: the projector's $1/q^2$ must cancel, which
  needs the joint polynomial dependence of the parametric numerators on the external momenta
  (the zeroth-order cancellation is proved, `formFactorProj₂_numerator_self`).
- **O2-23 (infrared limit).** Plan: per-unit infrared expansions at $q^2=0$. For each unit
  $U$, its contribution to the regulated $F_2^{(4)}(0)$ of O2-22 has the form
  $a_U\ln(m_\gamma/m)+b_U(\Lambda,M_f)+o(1)$ as $m_\gamma\to0^+$, at fixed $M_f$, with the
  $o(1)$ uniform in $\Lambda$ beyond a threshold (or combined with O2-17 in the joint limit
  of $m_\gamma\to0$, $\Lambda\to\infty$); uniformity in $M_f$ is not needed (D-37.4); then
  $a_{\mathrm L}=a_{\mathrm X}=a_{\mathrm{VP}}=0$ (BMR-I p. 834, item a), and p. 852),
  and $a_{\mathrm S}+a_{\mathrm C}=0$ by O2-15. **Caution (numerics, 11.3 and 11.6):** at
  finite $\Lambda$ the coefficients of S and C alone are $\pm1$ only up to terms
  $\pm c\,m^2/\Lambda^2$ ($c\approx0.67$), which cancel in S$+$C. So the expansion with
  $\Lambda$-independent $a_U$ holds for the groupings S$+$C, L, X, VP, not for S and C
  separately, and a joint limit in $(m_\gamma,\Lambda)$ exists for S$+$C but not for S or C
  alone. State the obligation on S$+$C (as O2-25 does). Conclusion: at fixed $M_1,M_2$ the regulated
  $F_2^{(4)}(0)$ has a limit as $(m_\gamma,\Lambda)\to(0,\infty)$, and that limit converges
  as $M_1,M_2\to\infty$ (O2-19), the order of D-37.4; its value is O2-25's. Theorem;
  **high** effort. BMR-II (1.23)–(1.33), p. 873–875, shows that for the ladder the
  $\lambda\to0$ limit does not commute with the dispersive integration (source): route A
  must keep $m_\gamma>0$ until after the parametric integrals are combined, as D-36 says.

### 5.6 Order of limits and the headline (ruled, D-37)

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

**Ruled order (D-37.1, D-37.4).** $\varepsilon\to0^+$ at fixed everything; then
$q^2\to0^+$ at fixed regulators, uniformly over on-shell pairs (O2-22); then
$(m_\gamma,\Lambda)\to(0,\infty)$ at fixed $M_1,M_2$; then $M_1,M_2\to\infty$ last, with
$c_1,c_2$ fixed by the Pauli–Villars conditions and no constraint on $M_2/M_1$ (O2-19). This
refines D-5's iterated order. The magnetic-moment definitions of the frozen model (the
response moments (R₀) and (L₅), and the source moment (L₇) with its packet limit) already
take $q\to0^+$ at fixed regulators, so they are unaffected; only the Pauli-component clause
changes shape.

**Headline (quantifier form, D-37.1).** For every $\eta>0$ there is $R_M$ such that for all
$M_1,M_2>R_M$ there are $\delta>0$ and $R$ (which may depend on $M_1,M_2$) such that for all
$m_\gamma\in(0,\delta)$, $\Lambda>R$ and all admissible counterterms (single real numbers
satisfying the order-$e^2$ conditions (Z₅), (Z₈), (K₀), D-37.3) there is $q_0>0$, depending
on the regulators, such that every form-factor pair of the order-5 1PI vertex $V^{\mu,[5]}$
(D-37.6) at every on-shell pair with $0<q^2<q_0$ has $|16\pi^4\hat F_2-A_1^{(4)}|<\eta$.

D-37.1 states the quantifier form with one pair of thresholds $(\delta,R)$ for "regulators
beyond the thresholds"; read with D-37.4 (masses removed last), the threshold for $M_1,M_2$
is chosen first and $(\delta,R)$ may depend on $M_1,M_2$, as written above. A version with
$(\delta,R)$ independent of $M_f$ would be a joint limit in the regulators, which D-37.4 did
not adopt; it would need the uniformity in $M_f$ that O2-19 and O2-23 no longer prove. This
reading, with $m_\gamma\to0$ and $\Lambda\to\infty$ taken jointly, is the one frozen provisionally in
packet T3 (D-41, `QED/Frozen/TwoLoop/VertexOrderFivePauliLimit.lean`); the author approved it as
written, confirming both choices (D-43).

The proof passes through the intermediate declarations of the former shape (b): the
$\exists!$ theorem of O2-22 and the regulated $F_2^{(4)}(0;m_\gamma,\Lambda,M_1,M_2)$ it
defines; the limit $F_2^{(4)}(0;M_1,M_2)$ as $(m_\gamma,\Lambda)\to(0,\infty)$ (O2-23); and
its limit as $M_1,M_2\to\infty$ (O2-19, O2-25). These imply the headline and give the
regulated two-loop number a name that later phases can reuse, but they are not the headline.

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
  **Status (2026-11-18): proved for the listed values and identities** (`QED/Polylog/`).
  $\mathrm{Li}_2,\mathrm{Li}_3$ and $\zeta(3)$ are defined as series, with
  `QED.Polylog.riemannZeta_three` linking $\zeta(3)$ to Mathlib. The values are `Li₂_one`,
  `Li₂_neg_one`, `Li₃_one`, `Li₃_neg_one`, `Li₂_one_half` and `Li₃_one_half`. The reflection
  `Li₂_add_Li₂_one_sub` holds on $[0,1]$, and the integral is
  `integral_log_mul_log_one_add_div`. The Landen identities
  `Li₂_one_sub_inv_add_Li₂_one_sub` and `Li₃_add_Li₃_one_sub_add_Li₃_one_sub_inv` are proved
  on $[\tfrac12,1]$ only, where every argument lies in $[-1,1]$. Further integrals that the
  reduction of O2-25 produces remain.
- **O2-25 (exact values of the units).** Prove the limits, at $q^2=0$ (after O2-22),
  $$\mathrm X\to\tfrac16-5\zeta(2)\ln2+\tfrac{13}6\zeta(2)+\tfrac54\zeta(3),\qquad
  \mathrm L\to\tfrac{11}{48}+\tfrac13\zeta(2),$$
  $$\mathrm S+\mathrm C\to-\tfrac73+2\zeta(2)\ln2-\tfrac12\zeta(3),$$
  and VP as in O2-18. These are the BMR-I p. 852 values (S and C combined, so that the
  logarithms cancel); they sum to the $q$-type value. **Highest risk of the phase.**
  Theorem, one per unit. It is not yet known whether the route-A units have exactly these
  limits: BMR assign each graph its subgraphs renormalized on shell, which matches the
  units of 5.2, but they work dispersively with $\lambda$ only and without Pauli–Villars.
  A numerical check of each unit in route-A form (section 11) finds the limits
  equal to these values within a few $10^{-5}$, with the counterterms of 5.1 and $\delta_1$
  from the charge condition. The risk that remains is the analytic evaluation itself.
  **Infrared cost:** S and C are not separately finite as $m_\gamma\to0$. Each must be
  evaluated at $m_\gamma>0$ in the form $a\ln(m_\gamma/m)+b+o(1)$, with $b$ exact (the
  expansion of O2-23), and only the sum has an $m_\gamma$-free limit. Splitting off the
  logarithm exactly before evaluating the remainder is harder than evaluating a finite
  integral. L and X are evaluated at $q^2=0$, where they are infrared finite (5.5). Method
  options:
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
  order of limits of D-37 (5.6: $(m_\gamma,\Lambda)\to(0,\infty)$, then $M_1,M_2\to\infty$),
  and from it the quantifier-form headline of 5.6 via O2-22 and O2-27. Since $r=e^2/4\pi^2$,
  $[r^2]F_2=16\pi^4[e^4]F_2$. Theorem by combination; low once O2-1–O2-25 and O2-27 hold.

## 7. Obligations, carriers and kinds

The last column lists the obligations each one uses; the numbering follows the sections
(except O2-27, added for D-37.3 and stated in 5.1), and the proof order must respect this
column.

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
| O2-16 | The overall divergence feeds $F_1$ only (no order-5 tree counterterm, D-37.3) | theorem | O-8; CK-UV p. 3995 | low | O2-17, O2-21 |
| O2-17 | UV cancellation per unit as $\Lambda\to\infty$ | theorem | CK-UV (2.11)–(3.40); AKN (70)–(79) | high | O2-10, O2-13, O2-15 |
| O2-18 | VP unit: spectral form, value $\frac{119}{36}-\frac{\pi^2}3$ | theorem | Srednicki (62.25); BMR-II (1.1)–(1.10) | moderate | O2-8, O2-13, O2-14 |
| O2-19 | Regulator-fermion decoupling $M_f\to\infty$, taken last (D-37.4; derivative bound on the limited VP function) | theorem | — | moderate | O2-18 |
| O2-20 | Covariance of the order-5 vertex, via the parametric form | theorem | CK-R (30)–(31) | moderate–high | O2-7, O2-10 |
| O2-21 | No $q^\mu$ term (mirror pairs or Ward identity); $\exists!$ form-factor pair at order 5 and per unit | $\exists!$ theorem | packet 2 | moderate–high | O2-11, O2-14, O2-20 |
| O2-22 | $q^2\to0^+$ limit of the order-5 $\hat F_2$ at fixed regulators, uniform over pairs; regulated $F_2^{(4)}(0)$ | $\exists!$ theorem, then definition | BMR-I (1.20), p. 834 c); BMR04 (117) | moderate | O2-12, O2-20, O2-21 |
| O2-23 | Infrared limit at fixed $M_f$; per-unit expansions, log cancellation via O2-15 | theorem | BMR-I (1.20), p. 834–835, p. 852; AKN (85)–(95) | high | O2-15, O2-17, O2-18, O2-19, O2-22 |
| O2-24 | $\mathrm{Li}_2,\mathrm{Li}_3$ and their special values | infrastructure | BMR-I App. A | moderate | — |
| O2-25 | Exact limits of the units | theorem | BMR-I p. 852 (targets) | **highest** | O2-23, O2-24 |
| O2-26 | Assembly: $16\pi^4F_2^{(4)}(0)\to A_1^{(4)}$ in the D-37 order; the quantifier-form headline | theorem | D-37.1, D-37.4 | low | O2-1–O2-25, O2-27 |
| O2-27 | Order separation for single real counterterms: $\delta_i=e^2d_i$, $[e^4]F_2$ as a coefficient (D-37.3) | theorem | (Z₆), (Z₉), (K₀) | low (moderate if a condition is truncated at order 5) | O2-2, O2-9 |

**Carriers needed for exact declarations** (none exists yet):

| Carrier or definition | Kind | Notes |
| --- | --- | --- |
| Successor model keeping `Params` with single real counterterms and the frozen order labels (no graded coefficients, no order-5 counterterm kind) | meaning-carrying definition | D-37.3; order separation O2-27; packet 6a's objects must embed (O2-9, as (Y₁) did for packet 5) |
| Two-loop routing (two chords) and `lineMomentum₂` | definition | O2-5 |
| Joint two-loop energy-first integral on $(\mathbb R^4)^2$ | definition (generic operation) | D-37.5; O2-6; returns 0 off integrability, like (D), so statements assert integrability |
| Two-loop `contractionValue` and the order-5 1PI function $V^{\mu,[5]}$ | source-facing definitions | sum over contractions of total order exactly 5 |
| Renormalized order-5 1PI vertex with $\delta_i$ from (Z₆), (Z₉), (K₀) | definition | D-37.6; reuses frozen predicates; (Z₈) is now a premise; $\delta_i=e^2d_i$ by O2-27 |
| Projector $P_2$ | definition | O2-11; per-class $F_2[G]$ |
| Form factors at order 5 from O2-21 | $\exists!$, then definition | as packet 2 |
| Regulated $F_2^{(4)}(0;m_\gamma,\Lambda,M_1,M_2)$ from O2-22 | $\exists!$, then definition | intermediate (not in the headline), with a characterization theorem |
| $\mathrm{Li}_2$, $\mathrm{Li}_3$, $\zeta(3)$ value | infrastructure | O2-24 |
| Headline | theorem | quantifier form of 5.6 on the order-5 1PI vertex: $q^2\to0^+$ first at fixed regulators, then $(m_\gamma,\Lambda)\to(0,\infty)$, then $M_1,M_2\to\infty$ (D-37.1, D-37.4, D-37.6; section 8) |

As at one loop, Lean's integral and `limUnder` return junk values off their domains, so the
source-facing statements must assert integrability or use `Tendsto`-style conclusions.

## 8. Rulings (D-37)

The six design questions raised by the first version of this document were ruled on by the
author on 2026-11-17 (D-37 in [DECISIONS.md](campaign/DECISIONS.md)). They are recorded here
in D-37's numbering, with the consequences for the plan.

1. **Order of limits and headline form (D-37.1; was question 6, with question 3).** At order
   $e^5$ the joint limit in $q^2$ and $m_\gamma$ does not exist: for $q^2\ne0$ the order-$e^4$
   Pauli form factor carries an infrared logarithm $\sim q^2\ln m_\gamma$ (BMR-I (1.20),
   p. 834; section 5.6). So $q^2\to0^+$ is taken first at fixed regulators, uniformly over
   on-shell pairs, as in D-5. The headline uses the quantifier form of 5.6. The one-loop
   pattern of (I)/(H), one $\delta$ bounding both $q^2$ and $m_\gamma$, is not used.
   *Consequence:* O2-22 is required; the regulated $F_2^{(4)}(0)$ it defines is an
   intermediate declaration, not the headline.
2. **Ward identity (D-37.2; was question 1).** The one-loop identity
   $\delta_1^{(2)}=\delta_2^{(2)}$ ($Z_1=Z_2$), needed for the infrared cancellation between
   S and C, is proved as a theorem at fixed regulators from the frozen on-shell conditions,
   not imposed. Imposing it would be a smuggled hypothesis; a closed-form computation of
   both constants remains a cross-check. *Consequence:* O2-15, with the route given there
   (differential identity, differentiation under the one-loop integral, in the
   $\varepsilon\to0^+$ limit or on the parametric closed forms).
3. **Counterterms (D-37.3; was question 2).** Each counterterm stays a single real number,
   and the expansion is truncated. Order-graded coefficients and a formal polynomial ring in
   $e$ were not adopted, and no order-5 counterterm kind is introduced, so the order-5 1PI
   function has no tree counterterm (3.2, O2-16). Separating the orders is a proof
   obligation. *Consequence:* O2-27. With the frozen one-loop conditions (Z₆), (Z₉), (K₀),
   homogeneity gives $\delta_i=e^2d_i$, so $V^{\mu,[5]}$ is $e^5$ times an $e$-independent
   matrix and $[e^4]F_2:=\hat F_2$ is a coefficient, with no limit in $e$. Should a
   condition be imposed on an order-5 function, the extraction needs the more delicate
   item 3 of O2-27.
4. **Regulator fermions (D-37.4; was question 3).** Their masses are removed last: first
   $q^2\to0^+$, then $m_\gamma\to0$ and $\Lambda\to\infty$, then $M_1,M_2\to\infty$, with
   $c_1,c_2$ fixed by the Pauli–Villars conditions and no constraint on $M_2/M_1$. A joint
   limit in $(m_\gamma,\Lambda,M_1,M_2)$ was not adopted. *Consequence:* O2-19 bounds the
   already-limited one-flavour VP function and needs no uniformity in $m_\gamma$ or $\Lambda$;
   O2-23 works at fixed $M_f$ and needs no uniformity in $M_f$. In the quantifier form the
   threshold for $M_1,M_2$ comes first and $(\delta,R)$ may depend on $M_1,M_2$ (5.6).
5. **Prescription (D-37.5; was question 4).** The two-loop value is the joint energy-first
   integral: both loop energies first, then all six spatial components, then
   $\varepsilon\to0^+$. It is invariant under changes of loop momenta (O2-6), its energy
   integral is elementary (4.3), and the frozen (D) is its one-loop case (O2-9).
   *Consequence:* "nested equals joint" is a theorem for the insertion classes S₊, S₋ and VP
   (O2-8), where the frozen one-loop Σ and Π are reused.
6. **Amplitude (D-37.6; was questions 5 and 6).** The first two-loop headline is stated on
   the order-$e^5$ 1PI vertex (62.39), the sum over contractions of total order exactly 5,
   with the counterterms fixed by the on-shell order-$e^2$ conditions (Z₅), (Z₈), (K₀). An LSZ
   restatement can follow later, with an equivalence theorem as packet 6c did at one loop.
   *Consequence:* the LSZ form, when it comes, needs more than the 1PI vertex: the two-loop
   self-energy with on-shell conditions at order $e^4$ (otherwise the LSZ limit fails or has
   the wrong residue), the two-loop photon leg, an order-$e^5$ charge condition, and the
   order-$e^5$ term $\Pi(q^2)F_2^{(2)}(q^2)$ from the one-loop photon leg times the one-loop
   vertex, which reaches $F_2$ at $q\ne0$ and vanishes as $q\to0$ only through (Z₈) or the
   background-field factor $q^2/(q^2+m_\gamma^2)$ of 5.3. With single real counterterms
   these conditions are of the kind covered by item 3 of O2-27. Tadpoles (O2-4) also enter
   only there.

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

## 11. Numerical validation of the route-A units

**Status:** numerics, run 2026-11-17 (numpy 2.5.3, mpmath 1.3.0). This is a sanity check of the
plan of sections 5.1–5.6, as O2-25 recommended before any declaration is drafted. It is
evidence, not proof, and it supports no obligation. The script is
[`scripts/numerics/two_loop_units.py`](../scripts/numerics/two_loop_units.py). Its docstring
gives the modes (`checks`, `uv`, `ir`, `vp`, `fit`), the run times (minutes to about half an
hour on 4 cores) and how to replay every table below.

### 11.1 What was computed

For each unit of 5.2 the script computes its contribution to $[r^2]F_2$ as $q\to0$ at fixed
$m_\gamma$, $\Lambda$ (and $M_1,M_2$ for VP). The counterterms are those of route A:

- $\delta_2,\delta_m$ from the on-shell conditions with the Pauli–Villars photon;
- $\delta_1$ from the charge condition, in its 1PI form $F_1(0)=1$ at order $e^3$;
- $\delta_3$ from $\Pi(0)=0$.

The units are VP ($+\delta_3$), S $=$ S₊ $+$ S₋ $+$ their $(\delta_2,\delta_m)$ insertions,
C $=$ C₊ $+$ C₋ $+2\delta_1F_2^{(2)}$, L $=$ ladder $+\delta_1F_2^{(2)}$, and X.

Method:

- **Representation.** Each graph is written in the covariant Feynman-parametric form of 4.4,
  with the 8-dimensional loop integral done in closed form, including the
  $\ell\ell\to-g\,(U^{-1})\Delta/(2(n-5))$ rule. These numerics test the **parametric values**,
  not the energy-first prescription. O2-7, O2-8 and O2-20 are untested here.
- **Photon lines.** Each Pauli–Villars photon is the difference of the masses $m_\gamma$ and
  $\Lambda$, combined point by point in the integrand.
- **Extraction of $F_2$.** The vertex is expanded to first order in $q$, and the exact
  two-structure projector $P_2$ (O2-11) is applied as $q\to0$. The $O(q^2)$ part of the
  vertex drops out exactly, because $(\not p+m)(\gamma_\mu-p_\mu/m)(\not p+m)=0$ on shell.
  So this is the $q^2\to0^+$ limit at fixed regulators of D-37.1, taken exactly.
- **Merged lines.** Lines with the same loop routing and mass are merged. The integrand is
  affine in the split, so the split is evaluated at its midpoint.
- **Quadrature.** Sector decomposition with sigmoidal Gauss–Legendre maps, in 3 to 4
  dimensions. For L and C the simplex is nested around the UV subgraph, with a logarithmic
  grid in its scale. Each graph is evaluated on two grids. The quoted error is
  $|\text{fine}-\text{coarse}|$, which is a heuristic, not a bound.
- **S in insertion form.** The on-shell renormalized Pauli–Villars self-energy is a mass
  superposition,
  $\Sigma_R(k)=\tfrac r4\int_0^1\!\frac{dx}x\int_{m_\gamma^2}^{\Lambda^2}\!d\mu\,
  (\not k-m)^2(\alpha\not k+\beta)/(M^2-k^2)$, with $M^2=m^2/(1-x)+\mu/x$. With its two
  adjacent propagators it becomes a single line of mass $M$. The S unit is then an outer
  one-loop vertex integrated over $(x,\mu)$. Its integrand has no power-like cancellation.
- **VP.** Exact partial fractions in $k^2$ of $\Pi_R k^2D^2$, with the spectral form of O2-18
  and the one-loop $F_2$ of a massive photon and its mass derivative (mpmath, 30 digits).

### 11.2 Checks of the machinery

| Check | Result |
| --- | --- |
| $P_2$ on $\gamma^\mu$ and on $i\sigma^{\mu\nu}q_\nu/2m$ | $0$ and $1$ (to $10^{-14}$) |
| One-loop $F_2/r$ with photon mass $\lambda=10^{-4},0.3,1$ against $\int_0^1\frac{x^2(1-x)}{x^2+(1-x)\lambda^2}dx$ | agree to 12 digits |
| Ward identity at fixed regulators: $\delta_1=-F_1^{\rm loop}(0)$ (engine) against $\delta_2=\partial\Sigma/\partial\not p$ (closed form) at $(m_\gamma,\Lambda)=(0.1,10),(0.03,100),(0.5,3)$ | equal to 12 digits (e.g. $0.238801665709$) |
| S insertion form against bare S± two-loop graph $+$ counterterm graphs $i(\not k\delta_2-\delta_m)$, at $(0.5,3)$ and $(0.2,10)$ | $-0.178791$ vs $-0.178793$; $-0.614740$ vs $-0.614739$ |
| Mirror pairs at $(0.1,10)$ | C₊ $=$ C₋ to 8 digits; S₊ $=$ S₋ |
| Overall-divergence patterns (two contractions, $\propto\gamma^\mu$) | $P_2$ gives $0$ |
| X at $m_\gamma=0$, $\Lambda=\infty$ (UV finite, IR finite at $q=0$) | $-0.467632$; BMR $-0.467645$ |
| VP at $m_\gamma=0$, $\Lambda=\infty$, one flavour | $\frac{119}{36}-\frac{\pi^2}3$ to $10^{-30}$ |

### 11.3 Ultraviolet: no $\ln\Lambda$ after the counterterms

Units and bare graphs at $m_\gamma=10^{-2}$:

| $\Lambda$ | $\delta_1/r$ | L bare | L | C₊$+$C₋ bare | C | S | X | VP |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 10 | 2.342935 | −0.469920 | 0.659617 | 1.647889 | 3.906963 | −4.508029 | −0.369463 | 0.014484 |
| 30 | 1.801887 | −0.203923 | 0.669635 | 2.178375 | 3.925490 | −4.568721 | −0.369780 | 0.015509 |
| 100 | 1.200899 | 0.088615 | 0.671210 | 2.761561 | 3.926751 | −4.578164 | −0.369667 | 0.015665 |
| 300 | 0.651681 | 0.355210 | 0.671381 | 3.294396 | 3.926738 | −4.579207 | −0.369622 | 0.015679 |
| 1000 | 0.049705 | 0.647289 | 0.671404 | 3.878490 | 3.926720 | −4.579348 | −0.369610 | 0.015681 |

Quadrature errors: L $3\times10^{-8}$, C $10^{-4}$, S $10^{-5}$, X $2\times10^{-6}$.

- **Bare graphs.** $\delta_1$ falls by $\tfrac12\ln10$ per factor 10 in $\Lambda$
  ($\delta_1\ni-\tfrac12r\ln\Lambda$). The bare L and C graphs grow by $0.56$ and $1.12$,
  i.e. by $\tfrac12\ln10\,F_2^{(2)}$ and twice that, as the counterterms require.
- **Units.** Every unit settles. Successive differences shrink by about 9 per factor 3 in
  $\Lambda$, which is the $\Lambda^{-2}$ behaviour expected of the decoupling terms. Claim
  (a) of the plan holds for every unit.
- **Smaller photon mass.** At $m_\gamma=10^{-4}$ (Λ = 30, 100, 300, 1000) the same holds:
  - S: −9.283640, −9.296159, −9.297476, −9.297649
  - C: 8.639060, 8.643385, 8.643645, 8.643658
  - L: 0.773189, 0.774780, 0.774952, 0.774975
  - X: −0.465377, −0.465273, −0.465228, −0.465216
- **A finding for O2-23.** For S and C separately, the finite-$\Lambda$ remainder depends on
  $m_\gamma$:
  - $S(100)-S(1000)=1.18,1.34,1.49,1.64\times10^{-3}$ at $m_\gamma=10^{-2},10^{-3},10^{-4},10^{-5}$.
  - That is about $0.67\,(m^2/\Lambda^2)\ln(m/m_\gamma)$, and C carries the opposite term.
  - S$+$C is free of it at every $\Lambda$.
  - L, X and VP have $m_\gamma$-independent remainders: $1.9\times10^{-4}$,
    $5.7\times10^{-5}$ and $1.6\times10^{-5}$ between $\Lambda=100$ and $1000$.

### 11.4 Infrared and the limits, against BMR-I p. 852

Units at $\Lambda=1000$, as functions of $m_\gamma$ ($m=1$; quadrature errors in brackets;
VP has error below $10^{-9}$):

| $m_\gamma$ | VP | S $-\ln m_\gamma$ | C $+\ln m_\gamma$ | S$+$C | L | X | sum |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $10^{-2}$ | 0.015681 | 0.025822 (1e-5) | −0.678450 (1e-4) | −0.652628 | 0.671404 | −0.369610 | −0.335153 |
| $3\cdot10^{-3}$ | 0.015687 | −0.043091 | −0.610723 (6e-5) | −0.653815 | 0.734472 | −0.427041 | −0.330698 |
| $10^{-3}$ | 0.015687 | −0.070747 | −0.583213 (2e-5) | −0.653960 | 0.759700 | −0.450664 (2e-5) | −0.329236 |
| $3\cdot10^{-4}$ | 0.015687 | −0.083037 (3e-5) | −0.570944 (2e-5) | −0.653981 | 0.771009 | −0.461412 (3e-5) | −0.328697 |
| $10^{-4}$ | 0.015687 | −0.087308 (1e-4) | −0.566683 (4e-5) | −0.653991 | 0.774975 | −0.465216 (4e-5) | −0.328545 |
| $3\cdot10^{-5}$ | 0.015687 | −0.089040 (3e-4) | −0.564940 (3e-5) | −0.653980 | 0.776612 | −0.466794 (4e-5) | −0.328475 |
| $10^{-5}$ | 0.015687 | −0.089672 (6e-4) | −0.564368 (3e-5) | −0.654040 | 0.777153 (3e-5) | −0.467317 (4e-5) | −0.328517 |

**Fits.** Each unit was fitted to $a_U\ln m_\gamma+b_U+m_\gamma(c_1\ln m_\gamma+c_0)$, with an
optional $m_\gamma\ln^2m_\gamma$ term, on the points with $m_\gamma\le10^{-3}$, $3\cdot10^{-3}$
and $10^{-2}$; the spread over these fits is quoted. The leading correction is
$O(m_\gamma\ln m_\gamma)$; for X this is confirmed down to $m_\gamma=10^{-6}$. The free fits
give $a_U$, and $b_U$ was then refitted with $a_U$ fixed to the nearest integer.

| Unit | fitted $a_U$ | BMR $a$ | $b_U$ ($\Lambda=1000$) | BMR-I p. 852 | difference |
| --- | --- | --- | --- | --- | --- |
| VP | $0.0000$ | 0 | $0.015687$ | $0.015687$ | $-2\times10^{-7}$ |
| S | $+1.0001\pm0.0002$ | $+1$ | $-0.089994\pm6\times10^{-5}$ | $-0.089978$ | $-2\times10^{-5}$ |
| C | $-1.0000\pm0.0001$ | $-1$ | $-0.564030\pm8\times10^{-5}$ | $-0.564021$ | $-9\times10^{-6}$ |
| L | $0.0000\pm0.00002$ | 0 | $0.777475\pm2\times10^{-5}$ | $0.777478$ | $-3\times10^{-6}$ |
| X | $0.0000\pm0.00002$ | 0 | $-0.467631\pm2\times10^{-5}$ | $-0.467645$ | $+1.5\times10^{-5}$ |
| S$+$C | $0.0001\pm0.0002$ | 0 | $-0.654020\pm8\times10^{-5}$ | $-0.653999$ | $-2\times10^{-5}$ |

What the fits show:

- **Logarithm coefficients.** They are $a_{\mathrm S}=+1$, $a_{\mathrm C}=-1$ and
  $a_{\mathrm L}=a_{\mathrm X}=a_{\mathrm{VP}}=0$ to $2\times10^{-4}$, and they cancel in the
  sum. This is claim (b).
- **Limits.** Every limit agrees with BMR-I p. 852 to within $2\times10^{-5}$, which is
  inside the quadrature and extrapolation uncertainty (a few $10^{-5}$). This is claim (c).
- **Remaining $\Lambda=1000$ effect.** The remainder of 11.3 is at most about $2\times10^{-5}$.
- **Totals.**
  - The sum of the five limits is $-0.32849\pm9\times10^{-5}$, against
    $A_1^{(4)}=-0.328479$.
  - The $q$-type part, S$+$C$+$L$+$X, is $-0.344176\pm9\times10^{-5}$, against
    $-0.344166$.
  - The VP part is $0.0156874$, against $\frac{119}{36}-\frac{\pi^2}3=0.0156874$.
- **AKN cross-check.** $\Delta M_{4a}$ of AKN (96) is not reproduced here. It is a
  $K$-scheme quantity, and relating it to these units needs AKN's residual constant
  $L_2^R$, which route A does not produce. The AKN-form check of section 9 stands as before.
  The present engine was checked instead against BMR's per-graph values. Through AKN (92)
  and (93) the Ward–Takahashi groupings are $a_{4a}=\mathrm X+\mathrm C$ and
  $a_{4b}=\mathrm L+\mathrm S$, which sum to the AKN (97) total.
- **Earlier run at $\Lambda=100$.** At $\Lambda=100$ (same $m_\gamma$ grid down to $10^{-5}$),
  the fits gave $b_{\mathrm S}=-0.08835$ and $b_{\mathrm C}=-0.56446$. These are off by
  $+1.6\times10^{-3}$ and $-4\times10^{-4}$. Those offsets are the finite-$\Lambda$ remainders
  of 11.3, including the $(m^2/\Lambda^2)\ln m_\gamma$ term. They are not a discrepancy, and
  S$+$C at $\Lambda=100$ is off by the $\Lambda$-remainder alone.

**Pieces of S.** The insertion of $i\delta_m m$ on one internal line of the one-loop vertex
(single photon mass $\lambda$, $\Lambda=\infty$) gives $-0.4084,-0.4887,-0.4988,-0.4999$ per
unit $\delta_m$ at $\lambda=10^{-1},10^{-2},10^{-3},10^{-4}$. The $i\delta_2\not k$ insertion
gives $-0.795,-0.974,-0.997,-0.9997$. In $F_2$ at $q\to0$, neither piece has a power-like or
logarithmic infrared growth. The bare S₊ graph at $\Lambda=10$ is $0.522,0.622,0.684$ at
$m_\gamma=0.2,0.1,0.05$, with no growth like $1/m_\gamma$. The $+\ln m_\gamma$ of S comes from
the infrared logarithm of $\delta_2$ times the finite $\not k$ insertion.

### 11.5 Regulator fermions last (D-37.4)

- **VP limit.** With $m_\gamma\to0$ and $\Lambda\to\infty$ taken first, the VP unit with
  flavours $f=0,1,2$ minus its limit $\frac{119}{36}-\frac{\pi^2}3$ is:

  | $(M_1,M_2)$ | VP minus limit |
  | --- | --- |
  | $(3,5)$ | $-3.0\times10^{-3}$ |
  | $(10,20)$ | $-2.7\times10^{-4}$ |
  | $(30,60)$ | $-3.1\times10^{-5}$ |
  | $(100,300)$ | $-2.5\times10^{-6}$ |
  | $(1000,1001)$ | $-4.4\times10^{-8}$ |

  This is $O(m^2/M^2)$. The nearly degenerate pair, where $|c_f|\approx500$, behaves
  well, as the divided-difference form of O2-19 predicts.
- **Finite $\Lambda$ and $m_\gamma$.** At fixed $(m_\gamma,\Lambda)$ the electron loop alone is
  within $2\times10^{-5}$ of its limit for $(10^{-2},100)$ and $2\times10^{-9}$ for
  $(10^{-4},10^4)$. It has no logarithm in $m_\gamma$ or $\Lambda$.
- **(Z₈) is load-bearing.** Without (Z₈) the extra term $\Pi_{\rm reg}(0)F_2^{(\gamma)}$ would
  contain $|\Pi_{\rm reg}(0)/r|=\tfrac13|\sum_fc_f\ln M_f^2|=1.38,\ 2.98,\ 4.51$ at
  $(M_1,M_2)=(10,20),(100,300),(1000,3000)$. It grows like $\ln M_f$, as 5.3 says.

### 11.6 Verdict and consequences for the plan

Every unit, as defined in 5.2 with the route-A counterterms, behaves as the document claims:

- it is UV finite after its counterterms;
- its infrared logarithm has the BMR coefficient, and the logarithms cancel in S$+$C;
- its limit is BMR's per-graph value, to a few $10^{-5}$.

The Ward identity $\delta_1=\delta_2$ holds at fixed regulators, as D-37.2 requires. These are
numerical checks of the covariant parametric values. Items for the plan:

1. **O2-23 should use the infrared-finite groupings.** At finite $\Lambda$ the infrared
   coefficients of S and C alone are not $\pm1$ exactly: they carry
   $\pm0.67\,m^2/\Lambda^2$ (11.3). So "$a_U\ln m_\gamma+b_U(\Lambda)+o(1)$ with $a_U$
   independent of $\Lambda$" is false for S and C, and a joint limit
   $(m_\gamma,\Lambda)\to(0,\infty)$ of S or C alone fails along $m_\gamma=e^{-\Lambda^3}$.
   S$+$C, L, X and VP each have $a=0$ at every $\Lambda$ tested, to within the fit
   uncertainty of $2\times10^{-4}$. The obligation should therefore be stated for S$+$C
   (with $\delta_1=\delta_2$) and for L, X, VP, as O2-25 already groups S$+$C. Alternatively
   it should take $\Lambda\to\infty$ before $m_\gamma\to0$ for S and C, and D-37.4's
   "then $m_\gamma\to0$ and $\Lambda\to\infty$" should be read accordingly when the
   declaration is drafted.
2. **The linear infrared divergence of 5.5 is not seen.** It was not seen in $F_2$ at
   $q\to0$ for any piece (11.4, "Pieces of S"). The bullet has been restated. A power-like
   divergence may still occur in integrands before integration, as in the Ward-summed
   self-energy forms of AKN and AHKN, but none needs to cancel between S's terms after the
   $q\to0$ projection.
3. **The insertion form of S is a cleaner proof route** for O2-17 and O2-23 on S. Writing
   $\Sigma_R$ as a mass superposition with the factor $(\not k-m)^2$ cancels the adjacent
   propagators exactly and leaves a one-loop vertex with a heavy line. No subtraction between
   separately large terms remains: the bare S graph and its counterterms each contain
   $\ln\Lambda$, and $\delta_m\sim\ln\Lambda$.
4. **O2-18 has an exact finite-regulator form.** By partial fractions in $k^2$, the VP unit
   at finite $(m_\gamma,\Lambda,M_f)$ equals
   $$\int_0^1dv\,\rho(v)\sum_fc_f\Bigl[A\,f(\mu_v^2)
   +\sum_{c\in\{m_\gamma^2,\Lambda^2\}}\bigl(B_cf(c)-E_cf'(c)\bigr)\Bigr],$$
   where $f$ is the one-loop $F_2$ of a massive photon and $A,B_c,E_c$ are the
   partial-fraction coefficients of $k^4D^2/(k^2+\mu_v^2)$. The difference from the
   superposition at $m_\gamma=0$, $\Lambda=\infty$ is then explicit.
5. **The numerics do not touch the order-$e^5$ enumeration (O2-2).** They take the graph
   list of 3.1–3.2 as given. Nor do they test the energy-first prescription and its
   covariance (O2-7, O2-8, O2-20), O2-22's uniformity over on-shell pairs, or the
   non-commutation of $q^2\to0$ with $m_\gamma\to0$ (5.6).
