# Phase 5 plan: certified higher-loop families

[Campaign HQ](../README.md) · [Project outline](PROJECT-OUTLINE.md) ·
[Two-loop derivation](TWO-LOOP-DERIVATION.md) · [Two-loop units](TWO-LOOP-UNITS.md) ·
[Sources](SOURCES.md) · [Decisions](campaign/DECISIONS.md)

**Status (2026-11-18): planning document; design rulings in D-49** (Stage 0, then set (b); the
D-37 order with one regulator threshold; exact where feasible; minimal successor packets).
No declaration has been approved or frozen yet.
**Update:** task T2 is done. The value integral of set (b) (O3-13) and its enclosure (O3-14) are
proved at helper level (`QED/Chain/*.lean`: `integral_setB`, `aSetB_bounds`); the closed form still
needs a pinned literature source. Claims are labelled as at two loops:
**source** (read in a pinned PDF at the cited place), **numerics** (a floating-point or
multiprecision computation, evidence only; section 9), **recalled** (standard knowledge not
yet located in a pinned source, which must be pinned before anything relies on it).

Source abbreviations follow [TWO-LOOP-DERIVATION.md](TWO-LOOP-DERIVATION.md): **AHKN**
(`ahkn-2012`, "p. n" is PDF page n/36), **AKN** (`akn-2019`, page n of 27), **Pas**
(`passera-2007`, arXiv v2), **BMR-I/II**, **CK-R**, **CK-UV**. Write $r=\alpha/\pi$ and
$A^{(2n)}$ for a coefficient of $r^n$ in $a_e$.

## 0. Summary

- **Recommended first higher-loop family: the vacuum-polarization chains.** These are the
  one-loop vertex with its photon line dressed by $n\ge2$ one-loop lepton bubbles in a chain.
  At sixth order this is AKN's set (b), one diagram (AKN Fig. 3, p. 9). Its value is
  $(8/3)\zeta(3)-(4/135)\pi^2-943/324=0.002\,558\,524\,936\ldots$; that closed form was found
  by integer-relation detection on a 50-digit evaluation and still needs a pinned source. The same proof also gives:
  - the eighth-order I(a) diagram, $0.000\,876\,865\ldots$ (AHKN Table 1, p. 6; analytic,
    ref. [49]);
  - the tau-muon chain $A_3^{(6)}=1.909\,45(62)\times10^{-13}$ (Pas (21));
  - the $e\mu$ and $e\tau$ chains inside $A_2^{(6)}(\text{vac})$.

  It is the only bounded three-loop family that is both correctly renormalized by the
  frozen model's single real one-loop counterterms (D-37.3) and evaluable exactly with the
  existing polylogarithm library. Most of its proof is a re-run of the proved two-loop
  vacuum-polarization (VP) pipeline.
- **Do first, or in parallel, Stage 0:** the mass-dependent two-loop term
  $A_2^{(4)}(m_e/m_\mu)$, $A_2^{(4)}(m_e/m_\tau)$. Formally it closes the Phase 4 exit
  criterion, which includes "the specified mass-dependent contributions" (D-36.2 deferred
  them). It needs a multi-flavour successor of the model, which Stage 1b and Phase 6 also
  need. Apart from that it is the proved VP unit with a different loop mass.
- **What it costs.** Phase 4 needed about 320 Lean files and 105k lines of its own, out of
  594 files in `QED/`. Estimated sizes:
  - Stage 0: 30–60 files;
  - Stage 1 (electron chain): 70–130 files;
  - Stage 1b (flavours, $n$ bubbles): 20–40 more.

  The genuinely three-loop sets (fourth-order VP insertion; VP inside the two-loop vertex;
  light-by-light; the 50 diagrams without fermion loops) each cost a Phase 4 or more. The
  last two have no realistic exact route, and their honest target is a certified enclosure.
- **On the strategy review's quadrature pivot.** Adopt it as a staged research track for
  the light-by-light set and beyond, with a measured pilot first. Do not adopt it for the
  first family. It replaces only the final evaluation step, which was about 11% of Phase 4's
  lines. It does not replace the model-to-integral chain or the analytic regulator limits.

## 1. What Phase 4 leaves behind

Measured on the tree at `6940505`:

| Piece | Where | Size | Generic or per-diagram |
| --- | --- | --- | --- |
| Joint energy-first integral, routing by chords, contraction value, 1PI function | `QED/Frozen/TwoLoop/` (T1) | 22 frozen files | **Generic in the loop count.** `jointEnergyFirstIntegral L`, `IsChord`, `lineMomentum₂` and `contractionValue₂` are defined for `L = loopCount C`. Only the docstring scope and the source-facing theorems restrict to $K\le2n_f+n_A+3$ (two loops). |
| Invariances of the prescription; routing change; relabelling invariance; mirror | `JointIntegralInvariance`, `RoutingChange`, `RelabelInvariance`, `LimitMirror` | about 15 files | Generic in `L` (stated with `hL : loopCount C = L`) |
| Enumeration at order 5 | `Enumeration*`, `Relabel*` | 17 files, 7.1k lines | Per-order. Kernel `decide` over pair partitions; about 224 s and 3.5 GB (review §2.5). It does not scale to order 7. |
| Feynman formula ($N$ factors), Cheng–Wu, simplex merging, Symanzik criteria, positivity of $V$ | `QED/Integration/` | 34 files, 15.4k lines | Feynman, Cheng–Wu and merging are generic. The energy formula is 2D only, and the spatial formula is 6D only. The criteria and positivity are stated per class matrix. |
| Numerators to degree 4, the projector, $q^2\to0^+$, covariance | `TwoLoopNumerator*`, `ParamNum*`, `PauliZero*`, `LimitCovariance*` | about 45 files | Partly generic (moment calculus), partly per class |
| VP class: nested form, spectral $\Pi_R$, the outer one-loop functional, regulator limits, decoupling of the regulator fermions | `VPHalf*`, `VPUnitNested*`, `NestedVP*`, `UnitVP*`, `VacuumPolarizationUnit*`, `*VP` | 43 files, 14k lines | **The template for every VP-insertion family.** It works for any loop mass (`vpFlavour`). |
| Units L, X, S + C: traces, reductions, limits, kernels | `UnitL*`, `UnitX*`, `UnitSC*`, `UnitC` | about 130 files | Per diagram. The masses parametrize the photon masses (equation (2.1) of TWO-LOOP-UNITS), which is reusable for a massive photon. |
| Evaluation: kernels, master integrals, polylogarithms | `UnitXXi*`, `UnitXKernel*`, `UnitX`, `UnitC`, `UnitLS`, `QED/Polylog/` | 46 files, 11.5k lines (about 11%) | Partly reusable: $\mathrm{Li}_2$, $\mathrm{Li}_3$, $\zeta(3)$, `dilogI` and eight masters |
| Interval arithmetic and box quadrature | `QED/Numerics/` | 8 files | Rational operations only (no $\log$, $\sqrt{}$ or $\exp$ intervals); 2D monotone box partitions |

Two consequences shape the plan. First, the model already defines the order-$e^7$ vertex
`onePIFunction₂ P 1 1 7 …`. What is missing is a ruling that declares its three-loop terms
source-facing, together with the theorems that make them meaningful. Second, the single
real counterterms of D-37.3 renormalize an order-$e^7$ term correctly only if every
divergent subgraph of its graph is one loop. Order-$e^4$ counterterms
$\delta_i^{(4)}$ do not exist in the model. Any family with a two-loop vertex, self-energy
or VP subgraph therefore needs a successor model (section 5, Q4–Q5). The order-7 1PI
function of T1 must never be presented as the sixth-order coefficient.

## 2. The sixth-order landscape

**The five gauge-invariant sets** (source: AKN Fig. 3, p. 9, rendered page checked;
AHKN Fig. 3, p. 3 shows the same five representatives):

| Set | Content | Diagrams | Divergent subgraphs | Published value (form) | Value in a pinned source? |
| --- | --- | --- | --- | --- | --- |
| (a) | fourth-order VP inserted in the one-loop vertex | 3 | two-loop VP (overlapping), one-loop vertex and self-energy inside the loop | analytic (Mignaco–Remiddi 1969, **to pin**) | no |
| (b) | two second-order VP bubbles in a chain on the one-loop vertex | 1 | two one-loop VPs | analytic; $(8/3)\zeta(3)-(4/135)\pi^2-943/324$ by numerics (section 9) | no (**to pin**) |
| (c) | one second-order VP inserted in the two-loop vertex without fermion loops | 12 | one-loop VP, vertex and self-energy; **two-loop** vertex and self-energy subgraphs containing the bubble | analytic (Barbieri–Remiddi 1974, **to pin**) | no |
| (d) | light-by-light (LbyL): an electron loop with four photons, the external one among them | 6 | none after summing the six (each is log divergent alone); with the model's regulator fermions each is finite | analytic (Laporta–Remiddi 1991, **to pin**); about $0.371$ (**recalled**) | no |
| (e) | no fermion loop | 50 | nested and overlapping vertex and self-energy subgraphs up to two loops; infrared | analytic (Laporta–Remiddi 1996, completing earlier work, **to pin**) | no |
| total | $A_1^{(6)}$ | 72 | | $=1.181\,241\,456\,587\ldots$, closed form with $\zeta(5)$, $\pi^2\zeta(3)$, $\pi^4$, $\mathrm{Li}_4(\tfrac12)$, $\ln^42$ | yes: Pas (14), p. 2; AHKN (2.8), p. 5; AKN Table 1, p. 4 |

Corrections to the brief, and source notes:

- **No pinned source gives per-set sixth-order values.** AKN lists only the diagram counts
  of the five sets and the total (Table 1, p. 4). The labels I–V (eighth order, 13
  subgroups; AHKN Table 1, p. 6; AKN Fig. 4, p. 9) and I–VI (tenth order, 32 sets; AHKN
  Table 2, p. 7) belong to higher orders.
- **AHKN is inconsistent with itself.** The caption of its Fig. 3 says "6 gauge-invariant
  groups", but the figure shows five representatives, matching AKN's "five gauge-invariant
  sets". This should be recorded in ERRATA-AND-DEVIATIONS when the family is pinned.
- The full analytic citation list for the sixth-order groups is Pas ref. [16], p. 5
  (source): Mignaco–Remiddi, Nuovo Cim. A 60 (1969) 519; Barbieri–Remiddi, Phys. Lett. B 49
  (1974) 468; Barbieri–Caffo–Remiddi, Phys. Lett. B 57 (1975) 460; Levine–Remiddi–Roskies,
  Phys. Rev. D 20 (1979) 2068; Laporta–Remiddi, Phys. Lett. B 265 (1991) 182; Laporta,
  Phys. Rev. D 47 (1993) 4793 and Phys. Lett. B 343 (1995) 421; and Laporta–Remiddi, Phys.
  Lett. B 379 (1996) 283. Which paper holds set (b)'s closed form is not yet established.

**Experimental relevance.** Compare each contribution with the uncertainty $1.3\times10^{-13}$
of the current $a_e$ measurement (outline source 3). Here $r^2=5.40\times10^{-6}$,
$r^3=1.25\times10^{-8}$, $r^4=2.91\times10^{-11}$.

| Term | Coefficient | Contribution to $a_e$ | / exp. uncertainty |
| --- | --- | --- | --- |
| set (b) | $0.002\,558\,5$ | $3.2\times10^{-11}$ | ≈ 250 |
| $A_2^{(4)}(m_e/m_\mu)$ | $5.197\times10^{-7}$ | $2.8\times10^{-12}$ | ≈ 22 |
| $A_2^{(6)}(m_e/m_\mu)$ | $-7.37\times10^{-6}$ (Pas (19)) | $-9.2\times10^{-14}$ | ≈ 0.7 |
| eighth-order I(a) | $8.77\times10^{-4}$ | $2.6\times10^{-14}$ | ≈ 0.2 |
| $A_2^{(4)}(m_e/m_\tau)$ | $1.84\times10^{-9}$ | $9.9\times10^{-15}$ | ≈ 0.08 |
| set (d) | ≈ $0.371$ (recalled) | $4.6\times10^{-9}$ | ≈ 36 000 |
| $A_1^{(6)}$ | $1.181$ | $1.5\times10^{-8}$ | ≈ 110 000 |

Every sixth-order set matters experimentally. The first family is therefore a genuine part
of the prediction, not a toy.

## 3. Candidate first families

Sizes are rough, in Lean files, against about 320 Phase 4 files. "Model" means work on the
frozen Wick model or its successor; "link" means the chain from the model to an explicit
integral; "evaluation" means the value of that integral.

### (a) Fourth-order VP insertion: set (a), 3 diagrams

- **Gauge invariance:** yes (any VP insertion is transverse).
- **Published value and form:** analytic, with $\zeta(3)$ (recalled). Source: Mignaco–Remiddi
  1969 (to pin); the spectral function is Källén–Sabry, Dan. Mat. Fys. Medd. 29 (1955) no. 17
  (to pin).
- **What carries over:** the whole outer half of the VP pipeline. Once the renormalized
  two-loop $\Pi^{(4)}_R$ has a spectral form, the set is a superposition of one-loop vertices,
  exactly as the one-bubble unit is (O2-18).
- **New mathematics:**
  - the two-loop VP function in the model, with its overlapping vertex and self-energy
    subdivergences inside a closed loop;
  - an order-$e^4$ photon condition $\Pi^{(4)}(0)=0$, which needs graded counterterms;
  - the Källén–Sabry spectral function, with $\mathrm{Li}_2$ and $\mathrm{Li}_3$ of a
    threshold variable;
  - a dispersion relation, or a direct parametric evaluation.
- **Size:** 100–200 files, plus the graded-counterterm successor. It is mostly a new
  "two-loop subgraph" machine. That machine is reusable later (eighth-order I(b)–I(d), II,
  III), but it is the hard part of three loops.

### (b) VP chains: set (b) and its relatives (recommended)

- **Diagrams:** set (b) is one diagram. The family "$n$ one-loop bubbles of flavours
  $f_1,\dots,f_n$ in a chain on the photon of the one-loop vertex" contains:
  - the eighth-order I(a) (1 diagram) and the tenth-order I(a) (1 diagram);
  - the tau-muon diagrams of $A_3^{(6)}$;
  - the mixed $e\mu$, $\mu\mu$, ... chains inside $A_2^{(6)}(\text{vac})$ and
    $A_2^{(8)}$.
- **Gauge invariance:** yes, for each $n$ and each multiset of flavours.
- **Published value and form:**
  - set (b): analytic, to pin. Numerics (section 9) give
    $(8/3)\zeta(3)-(4/135)\pi^2-943/324$ to 51 digits.
  - eighth-order I(a): $0.000\,876\,865\ldots$, analytic (source: AHKN Table 1, p. 6, ref.
    [49] Caffo–Turrini–Remiddi, Nucl. Phys. B 141 (1978) 302). Numerics give
    $151849/40824+(32/63)\zeta(3)-(2/45)\pi^4$ to 59 digits.
  - tenth-order I(a): $0.000\,470\,94(6)$, numerical (source: AHKN Table 2, p. 7). Numerics
    here give $0.000\,470\,905\,716\ldots$, $0.6\sigma$ from AHKN's value.
  - $A_3^{(6)}=1.909\,45(62)\times10^{-13}$ (source: Pas (21), p. 3; numerics reproduce
    $1.909\,446\times10^{-13}$).
- **Representation** (Lautrup–Peterman–de Rafael type, to pin; reproduced here from the
  pinned one-loop formulas): writing $\hat\Pi_M(s)=2\int_0^1t(1-t)\ln(1+t(1-t)s/M^2)\,dt$
  (Srednicki (62.25) normalized by $r$, Euclidean $s=k^2/m_e^2$),
  $$A_{\text{chain}}(f_1,\dots,f_n)=\binom{n}{n_e,n_\mu,n_\tau}\int_0^1(1-x)
  \prod_{i=1}^n\hat\Pi_{M_{f_i}}\!\Big(\frac{x^2}{1-x}\Big)\,dx .$$
  The case $n=1$ is the proved VP unit (`integral_vpUnit`, $119/36-\pi^2/3$).
- **What carries over:**
  - the nested-form proofs of the VP class (O2-8 for VP), the spectral form of the model's
    $\Pi_R$ (`vacuumPolarizationLoop_sub_zero`), the outer one-loop functional and its
    regulator limits (`vpUnitReg`, `UnitVPLink`), and the divided-difference decoupling of
    the regulator fermions (`abs_vpLimSum_sub_le`);
  - the generic invariances, routing and relabelling;
  - the polylogarithm library.
- **New mathematics:**
  - the three-loop scope of the model and integrability at three loops, for this family
    only;
  - nested equals joint with two inner loops;
  - the counterterm algebra $(\Pi_{\text{loop}}-\delta_3)^2$ over the four contraction types
    (bubble-bubble, bubble-$\delta_3$ twice, $\delta_3$-$\delta_3$);
  - decoupling for products of flavour-summed bubbles;
  - the weight-3 evaluation (weight 4 for $n=3$).

  No new master integrals, no elliptic pieces, no new counterterm kinds and no infrared
  problem: $\hat\Pi^2/s\sim s$ as $s\to0$.
- **Size:** 70–130 files for set (b), electron only; 20–40 more for flavours and general
  $n$, given Stage 0.

### (c) Mass-dependent two-loop term $A_2^{(4)}(m_e/m_\mu)$, $A_2^{(4)}(m_e/m_\tau)$

- **Diagrams:** one each, the VP class with a muon or tau loop (Pas Fig. 1, p. 1).
- **Gauge invariance:** yes.
- **Published value and form:** an exact closed form in $\mathrm{Li}_2$, Pas (10), p. 2
  (source), valid for all mass ratios with real parts taken for $x>1$; originally Elend 1966
  (to pin). Values:
  - $5.197\,386\,70(28)\times10^{-7}$ and $1.837\,62(60)\times10^{-9}$ (Pas (11)–(12));
  - $5.197\,386\,67(26)\times10^{-7}$ and $1.837\,98(34)\times10^{-9}$ (AHKN (2.6)–(2.7));
  - $0.519\,738\,676(24)\times10^{-6}$ and $0.183\,790(25)\times10^{-8}$ (AKN Table 1).

  The three differ only through the CODATA mass ratios they use. Numerics reproduce all
  six values from the spectral integral and from Pas (10), which agree to 15 digits (section
  9).
- **What carries over:** essentially all of the VP unit. The "regulator-fermion" function
  $g(\mu)$ of O2-19 *is* the heavy-lepton contribution at loop mass $\sqrt\mu$, with weight
  $c_f$ replaced by $1$.
- **New mathematics:**
  - a model successor with physical flavours (section 5, Q5);
  - the VP pipeline with loop mass different from the open-line mass, where `MassScaling`
    can no longer set both to 1;
  - the closed form (Pas (10)) for $y=m_e/m_\ell<1$, rewritten with $\mathrm{Li}_2$ at
    arguments in $[-1,1]$ through the inversion formula;
  - a certified enclosure over an input interval of the mass ratio. This needs $\log$ and
    $\mathrm{Li}_2$ interval bounds, or monotonicity plus rational bounds.
- **Size:** 30–60 files.
- **Assessment:** not higher-loop, but required by Phase 6 (22σ for the muon) and by the
  Phase 4 exit as worded. It is the cheapest way to build the multi-flavour model.

### (d) The full $A_1^{(6)}$ (72 diagrams)

- **Gauge invariance:** yes.
- **Published value and form:** analytic, Pas (14) (source; Laporta–Remiddi 1996, to pin).
  The numerical value $1.181\,259(40)$ is Kinoshita 1995 (recalled).
- **Requirements:** all five sets, so graded counterterms; a three-loop enumeration (72
  diagrams plus counterterm graphs, beyond kernel `decide`); three-loop parametric forms
  (the energy integral in odd loop number has half-integer powers again; section 4);
  infrared cancellations across topologies; weight-5 constants.
- **Size:** at least three to six Phase 4s, even with enclosures for (d) and (e). Not a first
  family.

### (e) Other bounded sets considered

- **The LbyL set (d) alone (6 diagrams).**
  - For: it needs no counterterms at all, has no subdivergence once the six are summed or
    each is regulated by the model's regulator fermions, and is infrared finite. It is
    therefore compatible with T1 once the three-loop scope is ruled.
  - Against: it is a genuine three-loop integral with 10 lines; its analytic value needs
    weight-5 functions (recalled), so exact is out of reach; the honest target is a
    certified enclosure of a parametric integral in 7–8 dimensions.
  - This is the best *first high-dimensional quadrature target*, not the best first family.
- **One second-order bubble in the two-loop vertex, set (c), as an enclosure.**
  - By the spectral form, each of the 12 diagrams is a Phase 4 unit with one photon of mass
    $\mu_v=2m/\sqrt{1-v^2}\ge2m$, integrated over $v$ with weight $\rho(v)$.
  - The hierarchical variables of TWO-LOOP-UNITS (2.1) already carry a general inner photon
    mass, and the outer photon mass enters as $\lambda^2(w-e)$.
  - Smooth 3D integrals result, a realistic certified-quadrature target. But the
    renormalization needs $\delta_1^{(4)},\delta_2^{(4)},\delta_m^{(4)}$ for the two-loop
    subgraphs containing the bubble.
  - This is the natural second family (Stage 3).
- **The mass-dependent LbyL $A_2^{(6)}(m_e/m_\mu,\text{lbl})=1.439\,445\,989(77)\times10^{-5}$**
  (Pas (16), source). Same difficulty as set (d), with a heavy loop that converges faster.
  Later.

## 4. Recommendation and staged path

| Stage | Target | Prerequisites | Value form | Size (files) |
| --- | --- | --- | --- | --- |
| 0 | $A_2^{(4)}(m_e/m_\mu)$, $A_2^{(4)}(m_e/m_\tau)$, two loops | flavour successor of the model (Q5 i) | exact closed form (Pas (10)) as a function of the mass ratio; enclosure at an input interval | 30–60 |
| 1a | **set (b), electron two-bubble chain**, three loops | three-loop scope ruling for T1 (Q4) | exact: $(8/3)\zeta(3)-(4/135)\pi^2-943/324$ | 70–130 |
| 1b | chains of any flavours and length $n$: $A_3^{(6)}$, the $e\mu$/$e\tau$ chain parts of $A_2^{(6)}$, eighth- and tenth-order I(a) | 0, 1a | exact for $n\le3$, electron; otherwise an explicit 1D integral plus a certified enclosure | 20–40 |
| 2 | graded counterterms $\delta_i=e^2d_i^{(2)}+e^4d_i^{(4)}$ with order-$e^4$ on-shell conditions; the two-loop LSZ lift of (HV₃) (D-44.1) | ruling on Q5 ii | model work, no new coefficient | 60–120 |
| 3a | set (a), fourth-order VP insertion | 2 | exact (spectral Källén–Sabry) | 100–200 |
| 3b | set (c), VP inside the two-loop vertex | 2, Phase 4 units at a massive photon | certified enclosure first; exact if the massive-photon units close | 150–300 |
| 4 | set (d), LbyL | three-loop parametric forms; high-dimensional certified quadrature (section 5.4) | certified enclosure | research; 200–500 |
| 5 | set (e), then the full $A_1^{(6)}$ | everything above; forest structure | certified enclosure | multi-year |

**Why the chain family first.**

1. **Correctly renormalized in the frozen model.** Its only divergent subgraphs are one-loop
   bubbles, and their counterterm $\delta_3$ is the frozen order-$e^2$ one fixed by (Z₈).
   With $\delta_3=e^2d_3$ the family's counterterm contractions give exactly
   $(\Pi_{\text{loop}}-\delta_3)^2=\Pi_R^2$. No order-$e^4$ condition is needed. Sets (a), (c)
   and (e) cannot be stated correctly without a successor model.
2. **Exact value within reach.** The integrand is a product of explicit one-loop functions
   against a rational weight; weight 3 for $n=2$, and $n=3$ needs only $\zeta(3)$ and $\pi^4$
   (numerics). Through the Landau variable $\beta=\sqrt{1+4/s}$ the bubble becomes
   rational-times-log, and the existing `QED/Polylog/` covers $\mathrm{Li}_2$, $\mathrm{Li}_3$
   and $\zeta(3)$.
3. **Maximal reuse.** The VP class pipeline (43 files, 14k lines) is the template, and the
   model-level invariances are already generic in the loop count.
4. **It exercises the three-loop model honestly.** It needs the three-loop scope, three-loop
   integrability and the $\varepsilon\to0^+$ limit, nested-equals-joint with two subloops,
   and counterterm products. It does not hide them.
5. **Meaningful and pinned comparison targets.** Set (b) is about 250σ of the experiment.
   The same theorem, parametrized by flavours, covers values that are already pinned (AHKN
   Table 1, Pas (21)).

**Honest limitation, to be stated with the result.** The chain family is the structurally
simplest three-loop set: a one-loop vertex with an inserted product of one-loop functions.
It exercises the model and the regulator machinery at three loops. It does not exercise
genuine three-loop integrals, overlapping divergences or forests. It is reported as
"sixth-order set (b) (1 of 72 diagrams)", a subset.

## 5. Route

### 5.1 Keep route A's semantics

Reuse route A unchanged:

- the 4D Pauli–Villars photon, the photon mass and the regulator fermions;
- energy-first loop integrals with the joint prescription (`jointEnergyFirstIntegral L` is
  already loop-generic);
- subtraction at fixed regulators, units grouped as "graph plus the counterterm insertions
  on its divergent subgraphs";
- the D-37 order of limits.

Changing the regularization (dimensional regularization, declined in D-36.1) would break
the chain to the frozen model, and nothing at three loops forces it. For the chain family
the reuse is direct. The value is the outer one-loop vertex of the photon function
$D\,[\Pi k^2D]^2$, obtained by nesting rather than by a three-loop parametric
representation. So the missing three-loop parametric formulas are not on the critical path
of Stages 0–1.

### 5.2 What changes at three loops

1. **The energy integral at odd loop number.** In polar coordinates
   $\int_{\mathbb R^L}(-t^{\mathsf T}At+w)^{-n}dt$ reduces to
   $\int u^{L/2-1}(w-u)^{-n}du$. For $L=2$ this is elementary (TWO-LOOP-DERIVATION 4.3). For
   $L=3$ it gives $(-w)^{3/2-n}$ with a branch, as at one loop, so the holomorphy argument of
   O-7 returns. A loop-generic formula with the slit-plane continuation, and the $9$D
   spatial formula, are infrastructure for Stage 4 and beyond.
2. **Subdivergences of two-loop subgraphs, overlapping divergences, forests.** These need
   graded counterterms (Q5 ii). A unit becomes "graph plus all counterterm insertions over
   its forests". With fixed regulators everything is finite, and only the $\Lambda\to\infty$
   cancellation per unit must be proved (the analogue of O2-17, now with nested and
   overlapping forests; CK-UV (2.11)–(3.40); AHKN sections 5 and 7).
3. **Infrared.** Self-energy subgraphs carry $\ln m_\gamma$ (and products of them) that
   cancel only across units of different topologies. The S + C mechanism generalizes
   through the Ward identity at order $e^4$, which is itself a new obligation.
4. **Enumeration.** Order 7 has 72 vertex diagrams plus counterterm graphs. Kernel `decide`
   over pair partitions is out of reach. Family theorems instead need an orbit argument: a
   trivial stabilizer gives coefficient one per class, as the review suggested (§2.5). No
   full order-7 enumeration is needed for a family headline.
5. **Evaluation.** Weight-5 constants ($\zeta(5)$, $\mathrm{Li}_4(\tfrac12)$, $\ln^42$,
   Pas (14)) and, for sets (d) and (e), no realistic exact route by hand-guided reductions.

### 5.3 Where exact evaluation is feasible

| Family | Exact feasible? | Reason |
| --- | --- | --- |
| VP chains, $n\le3$, electron | yes | weight ≤ 4, explicit 1D integrand; constants identified (section 9) |
| $A_2^{(4)}(x)$ | yes | published closed form with $\mathrm{Li}_2$ (Pas (10)) |
| heavy-flavour chains, $n\ge2$ | as a function of the ratios, laborious; the explicit 1D integral is the natural statement | closed forms "too long to be listed" for the related $A_2^{(6)}$ (Pas, p. 2) |
| set (a) | yes, with effort | spectral Källén–Sabry; weight 3 |
| set (c) | uncertain | weight 4; needs the Phase 4 units at a massive photon as functions of $\mu$ |
| sets (d), (e), full $A_1^{(6)}$ | no (not by this campaign's methods) | weight 5; Laporta–Remiddi needed computer-algebra reductions over thousands of integrals |

### 5.4 The review's quadrature pivot, weighed

The review (REPORT §5.3, §7 item 12) proposes, from three loops on, Hepp-sector or
Zimmermann-forest parametric subtraction evaluated by Phase 3's certified quadrature, in
place of per-diagram polylogarithm reductions.

**Where it is right.**

- Per-diagram exact reductions do not scale past the chains and possibly sets (a) and (c).
- A generic sector-decomposition and power-counting theory in Lean would be a lasting asset.
  It generalizes the existing `NoSubdivergence*` criteria and positivity bounds into a
  Weinberg-type theorem.
- For sets (d) and (e) a certified enclosure is the only honest target this campaign can
  reach. D-36.3 ("certified higher-dimensional numerics is not the target") was a Phase 4
  ruling and needs a Phase 5 successor ruling (Q2).

**Where it is overstated.**

1. **It addresses a minority of the cost.** Evaluation was about 46 files and 11.5k of
   Phase 4's roughly 105k lines. The rest was the chain from the model to an explicit
   integral: enumeration, routing, integrability, the $\varepsilon\to0^+$ limit,
   parametrization, numerators, the projector, $q^2\to0^+$, covariance, counterterm
   identities, and the regulator limits with explicit dominating functions (for example the
   420 AM–GM certificates of the X link). Quadrature replaces none of these.
2. **Quadrature needs the limit first.** It encloses a fixed integral. The coefficient is a
   limit as $\varepsilon\to0^+$, $q^2\to0^+$, $m_\gamma\to0$, $\Lambda\to\infty$ and
   $M_f\to\infty$. An enclosure of the coefficient needs an explicit regulator-free integral
   *proved* to be that limit. Quadrature also needs quantitative bounds (derivatives or
   Taylor models up to singular faces), which are stronger than the dominated-convergence
   majorants Phase 4 used.
3. **Subtraction schemes need a proved scheme relation.** K-operation, R-subtraction and
   residual renormalization (AHKN (7.20), p. 34), or Volkov's subtraction (arXiv:1507.06435,
   to pin if pursued), produce integrands that differ from the on-shell units. Their relation
   to the model's on-shell counterterms is exactly the kind of identity route A proves unit
   by unit. The outline requires it (Phase 5: "establish the relationship between any
   computational intermediate scheme and the final stated renormalization prescription").
4. **Precision and dimension.**
   - Deterministic enclosures scale like $(1/\text{tol})^{d/k}$ boxes.
   - To matter experimentally, $A_1^{(6)}$ needs about $10^{-5}$ relative.
   - Phase 3 certified 2D integrals with rational integrands. There is no interval $\log$
     or $\sqrt{}$ yet, and no Taylor-model rule.
   - 7–8D enclosures at $10^{-5}$ inside Lean's kernel are an open research problem, not a
     schedule item.

**Recommendation.**

- Keep route A's model, limits and unit linkage throughout.
- Choose the evaluation per family:
  - exact where the integrand factorizes into one-loop functions (Stages 0–1, 3a);
  - certified enclosure of a *low-dimensional* proved representation where one exists
    (Stage 3b: the spectral variable plus the Phase 4 kernels, 3–4D);
  - generic sector-decomposed certified quadrature as a research track, entered through a
    pilot with a pass/fail measurement (section 8, task T3) before any commitment to sets
    (d) and (e).

## 6. Statement design questions for the author

These are the analogues of the D-37 questions, for the Stage 1a headline (provisional name
(HC₃)) and the Stage 0 headline ((HM₂)).

**Q1. Order of limits.** Proposed: unchanged from D-37:
- $\varepsilon\to0^+$;
- $q^2\to0^+$ at fixed regulators, uniformly over on-shell pairs;
- $(m_\gamma,\Lambda)\to(0,\infty)$ jointly at fixed regulator masses;
- the regulator-fermion masses last.

The chain family is infrared finite, so a joint $q^2$–$m_\gamma$ limit probably exists. But
proving it would need uniformity that buys nothing, and a common order across all family
headlines makes them additive later. With several physical flavours, the physical masses
are fixed parameters, not limits. Must every flavour's regulators be removed together
(one threshold $R_M$ for all), or flavour by flavour?

**Q2. Exact value or enclosure.**
- Proposed for (HC₃): the exact constant $A_{(b)}=(8/3)\zeta(3)-(4/135)\pi^2-943/324$
  (O3-1), with a companion enclosure theorem as for (U₂).
- For flavour-dependent coefficients: a theorem that the coefficient equals an explicit
  function of the mass ratio (closed form for $n=1$, the explicit chain integral for
  $n\ge2$), plus a separate certified enclosure on an input interval of the mass ratio.
  Never a statement that mixes the input uncertainty into the coefficient.
- A Phase 5 ruling should replace D-36.3: exact where feasible; certified enclosure,
  labelled as such, otherwise.

**Q3. How a family's contribution is defined.** Proposed: a new frozen definition
`vertexOrderSevenFamily P F …`. It is the partial sum of the order-exactly-7 terms of the
frozen `onePIFunction₂` (same $1/N!$, signs and `contractionValue₂`) over contractions
satisfying a family predicate `F`. Options for `F`:
- (i) a structural predicate. For example: every closed fermion loop has exactly two
  vertices; the open line has three vertices with the external photon in the middle; and
  removing the open line leaves a path of photon lines, loops and `photonCt` vertices
  joining its two outer vertices.
- (ii) the relabelling orbit of explicit representatives, as in O2-2.

(i) is easier to audit for meaning and (ii) easier to prove with. Proposed: freeze (i) and
prove (i) ⇔ (ii) as an obligation (O3-4). The family includes its counterterm partners
($\delta_3$ in place of a bubble). Flavours are summed inside the value (X₂₆), as now.

**Q4. Three loops inside T1.** T1's definitions are loop-generic, but its docstrings and
theorems declare the scope $K\le2n_f+n_A+3$. Proposed: a ruling that extends the
source-facing scope to the order-7 terms *of named families whose divergent subgraphs are
all one loop*, after an audit of `IsChord` and `lineMomentum₂` at $L=3$. It should state
explicitly that the full order-7 1PI function of T1 is *not* the renormalized sixth-order
vertex, because it lacks $\delta^{(4)}$. Alternatively, leave T1 untouched and put
everything into the successor of Q5.

**Q5. What the versioned successor must contain**, as a new packet with an embedding
theorem in the style of (Y₁), (T₁₃) and (T₁₄):
- (i) **Physical flavours** (Stage 0). A finite list of physical leptons with masses and
  unit loop weights, each with its *own* Pauli–Villars regulator pair satisfying the two
  conditions with that lepton's mass. Then the flavour sum splits into blocks; the electron
  block is exactly the frozen model, and each heavy block is a copy of the VP pipeline at a
  different loop mass. The alternative, one shared regulator pair for all flavours, couples
  the blocks and is not recommended. The open-line flavour is a parameter, which is needed
  for $a_\mu$ in Phase 6.
- (ii) **Graded counterterms** (Stage 2). $\delta_i=e^2d_i^{(2)}+e^4d_i^{(4)}$, with order-$e^4$
  on-shell conditions on the two-loop self-energy, vacuum polarization and charge. This
  reverses D-37.3 for the successor only. It is also what the two-loop LSZ lift (D-44.1)
  needs. Order separation (the analogue of O2-27) becomes a definition, no longer a
  theorem.
- (iii) Whether to unify the three frozen generations (review §2.2, §7 item 11) now. Proposed:
  no. Add successors with embedding theorems and leave the sealed anchors alone.

**Q6. The amplitude.** Proposed: the 1PI vertex, as in (HV₃), for (HC₃) and (HM₂). The LSZ
form adds photon-leg terms that vanish as $q\to0$ given (Z₈), and it waits for Q5 (ii).

**Q7. Normalization and conventions.** Proposed:
- $64\pi^6[e^6]F_2$ (since $r=e^2/4\pi^2$) for (HC₃);
- $16\pi^4[e^4]F_2$ for (HM₂);
- the mass ratio $y=m_e/m_\ell\in(0,1)$, as in AKN Table 1.

**Q8. Completeness claims.** Proposed: the headline needs only the family's own sum.
Relabelling invariance and coefficient one per class (O3-4) are obligations, but a theorem
that the order-7 vertex splits into the five sets is not, until Stage 5. The README states
"set (b), 1 of 72 sixth-order diagrams".

**Proposed shape of (HC₃)**, for orientation only:

> For every $\eta>0$ there is $R_M$ such that, for all regulator masses $M_1,M_2>R_M$ (with
> $c_1,c_2$ fixed by the Pauli–Villars conditions), there are $\delta>0$ and $R$ such that
> for all $m_\gamma\in(0,\delta)$, $\Lambda>R$, and all counterterms satisfying (Z₅), (Z₈)
> and (K₀), there is $q_0>0$ with the following property. Every form-factor pair of the
> order-$e^7$ vertex of the chain family (set (b) with its $\delta_3$ partners), at every
> on-shell pair with $0<q^2<q_0$, satisfies $|64\pi^6\hat F_2-A_{(b)}|<\eta$.

## 7. Obligations for the recommended family

Numbering O3-*. As before, each is something to **prove**, or, where marked, to **define**
after author approval, and none may be added as a hypothesis of a source-facing theorem.
"Reuse" names the Phase 4 template.

**Stage 1a: set (b), electron.**

| Id | Title | Kind | Source | Risk | Needs | Reuse |
| --- | --- | --- | --- | --- | --- | --- |
| O3-1 | Target constant $A_{(b)}=(8/3)\zeta(3)-(4/135)\pi^2-943/324$ | definition | to pin (section 8); numerics, 51 digits | low (once pinned) | — | `A1Four` (O2-1) |
| O3-2 | Three-loop scope: the loop formula $2L+2n_f+n_A=V_3+2$ at order 7; `IsChord` gives three chords; conservation and uniqueness of `lineMomentum₂` at $L=3$ | theorem + audit | CK-R (11)–(16) | low (the formulas are generic) | Q4 | `LoopBoundTwoExact`, `Routing` |
| O3-3 | Family predicate `F` and family vertex $V^{\mu}_{(b)}$ | definition (meaning-carrying) | AKN Fig. 3 (b) | moderate (audit of meaning) | Q3 | `VertexOrderFive` |
| O3-4 | The predicate equals the relabelling orbit of 4 representatives (bubble-bubble, bubble-$\delta_3$, $\delta_3$-bubble, $\delta_3$-$\delta_3$, with the `photonCt` slot pairings); trivial stabilizer, so coefficient one per class, by an orbit argument and not by kernel enumeration | theorem | Srednicki ch. 58 | moderate | O3-2, O3-3 | `RelabelInvariance`, `RelabelCounterterm*` |
| O3-5 | Integrability (T₉′) at $\varepsilon>0$ for every family contraction, at three loops; each bubble flavour-summed under the two PV conditions | theorem | — | moderate | O3-4 | `ClassIntegrableVP`, (HV₀) |
| O3-6 | Nested equals joint, with two inner one-loop functions: the family value at fixed $\varepsilon$ is the outer one-loop integral of $D\,(\Pi_{\rm loop}k^2D)^2$ and its $\delta_3$ partners; then $\varepsilon\to0^+$ | theorem | — | **high** (Fubini at three loops; the two-loop analogue needed sharper bounds) | O3-5 | `NestedVP*`, `VPUnitNested*` |
| O3-7 | Counterterm combination: the four types sum to $\Pi_R^2$ inserted, with $\delta_3=e^2d_3$ from (Z₈); order separation at order 7 | theorem | (62.10); D-37.3 | low | O3-6 | `VPUnitNestedD3`, O2-27 |
| O3-8 | Covariance, no $q^\mu$ term (the family is mirror-closed), $\exists!$ form-factor pair of $V^\mu_{(b)}$; projector | theorem | packet 2 | moderate | O3-6 | `LimitCovarianceVP`, `LimitMirrorVP`, `FormFactorClause` |
| O3-9 | $q^2\to0^+$ at fixed regulators, uniform over on-shell pairs; the regulated coefficient $F_{2,(b)}(0;m_\gamma,\Lambda,M_f)$ | $\exists!$ theorem, then definition | — | moderate | O3-8 | `PauliZeroLimitVP` |
| O3-10 | Explicit finite-regulator value: the outer functional of $\Pi_R(s)^2s^2D(s)^3$, with the spectral form of each bubble; Fubini on $[0,1]^3$ | theorem | Srednicki (62.25); O2-18 | moderate | O3-7, O3-9 | `UnitVPLink`, `vpFlavour_eq_outer` |
| O3-11 | $(m_\gamma,\Lambda)\to(0,\infty)$ at fixed $M_f$; partial fractions in $s$ as in TWO-LOOP-DERIVATION 11.6 item 4 | theorem | — | moderate | O3-10 | `tendsto_vpUnitReg` |
| O3-12 | Decoupling of the regulator fermions in products. Write the flavour-summed bubble as $\Pi_{R,e}+\Delta_M$, where $\Delta_M=c_1\Pi_{R,1}+c_2\Pi_{R,2}$ is a divided difference. The cross terms $2\Pi_{R,e}\Delta_M$ and $\Delta_M^2$ tend to $0$ as $\min M_f\to\infty$, with no constraint on $M_2/M_1$. | theorem | — | moderate (log growth of $\Pi_{R,e}$ against the decay of $\Delta_M$ for $s\lesssim M^2$; the region $s\gtrsim M^2$ has weight $O(M^{-2}\ln^2M)$) | O3-11 | `abs_vpLimSum_sub_le` |
| O3-13 | Exact value $\int_0^1(1-x)\hat\Pi(x^2/(1-x))^2dx=A_{(b)}$, with integrability | theorem | numerics; source to pin | moderate (weight 3; Landau variable; $\mathrm{Li}_2$, $\mathrm{Li}_3$ of rational arguments; endpoint cancellations) | O2-24 | `integral_vpUnit`, `QED/Polylog/` |
| O3-14 | Enclosure $A_{(b)}\in[0.002\,558\,52,\,0.002\,558\,53]$ | theorem | — | low | O3-1 | `a1Four_bounds` |
| O3-15 | Assembly: (HC₃) in the Q1 order from O3-9, O3-11, O3-12, O3-13 | theorem by combination | — | low | all | `pauliLimit_of_unitLimits` |
| O3-16 | Embedding: at order ≤ 5 the extended scope and any new anchors reproduce T1 | theorem | (T₁₄) | low | O3-2 | `OneLoopEmbedding` |

**Stage 0 and Stage 1b: flavours and longer chains.**

| Id | Title | Kind | Source | Risk | Needs |
| --- | --- | --- | --- | --- | --- |
| O3-M1 | Flavour successor `Params` with physical leptons, each with its own PV pair; embedding into T1 when the list is the electron alone | definition + theorem | Q5 (i) | moderate (meaning-carrying model change) | — |
| O3-M2 | The heavy-flavour VP unit: the VP pipeline with loop mass ≠ open-line mass (the mass-scaling step changes) | theorem | O2-18 | moderate | O3-M1 |
| O3-M3 | Closed form: the spectral integral equals Pas (10) for $y=m_e/m_\ell\in(0,1)$, rewritten with $\mathrm{Li}_2$ at $\pm y$, $y^2$ (inversion formula) | theorem | Pas (10), p. 2; Elend 1966 (to pin) | moderate | O2-24 |
| O3-M4 | (HM₂): $16\pi^4[e^4]F_2^{(\ell)}\to A_2^{(4)}(y)$ in the D-37 order, as a function of $y$ | theorem | Pas (11)–(12); AKN Table 1 | low–moderate | O3-M1–M3 |
| O3-M5 | Interval elementary functions ($\log$, $\mathrm{Li}_2$ on $[0,\tfrac12]$ by series with remainder), and an enclosure of $A_2^{(4)}$ on an input interval for $y$ (monotone in $y$) | infrastructure + theorem | CODATA ratio (Phase 6 input) | moderate | Phase 3 |
| O3-M6 | The chain theorem for any flavour multiset (multinomial factor from $1/(1-\sum\Pi)$), as the explicit 1D integral | theorem | Lautrup–Peterman–de Rafael (to pin) | low given 1a | O3-M1, O3-15 |
| O3-M7 | Eighth-order I(a): exact $151849/40824+(32/63)\zeta(3)-(2/45)\pi^4$ (numerics), against AHKN Table 1 | theorem | AHKN p. 6, ref. [49] | moderate (weight 4) | O3-M6 |
| O3-M8 | Certified enclosures for $A_3^{(6)}$ and the $e\mu$, $e\tau$ chains (1D integrals with log singular endpoints) | theorem | Pas (21) | moderate | O3-M5, O3-M6 |

## 8. Sources, risks and the first bounded task

### 8.1 Sources to pin

Already pinned and used here: AHKN (Table 1 p. 6, Table 2 p. 7, (2.6)–(2.8) p. 5, Figs. 3–4
p. 3, refs. p. 35); AKN (Table 1 p. 4, Figs. 3–4 p. 9); Pas ((10)–(21), pp. 2–3, refs.
p. 5); Srednicki (62.25).

To pin, by priority:

1. **The source of set (b)'s closed form.** Most likely in Mignaco–Remiddi, Nuovo Cim. A 60
   (1969) 519, or in Barbieri–Remiddi, Phys. Lett. B 49 (1974) 468. Confirm which; a
   secondary compilation with the per-set values is also wanted, e.g. M. Passera, J. Phys. G
   31 (2005) R75 (Pas ref. [14]), or T. Kinoshita (ed.), *Quantum Electrodynamics* (World
   Scientific, 1990).
2. B. E. Lautrup, A. Peterman, E. de Rafael, "Recent developments in the comparison between
   theory and experiments in quantum electrodynamics", Phys. Rep. 3 (1972) 193. This is the
   VP insertion and chain representation (**recalled** as the standard reference).
3. M. Caffo, S. Turrini, E. Remiddi, Nucl. Phys. B 141 (1978) 302 (eighth-order I(a),
   analytic; AHKN ref. [49]).
4. H. H. Elend, Phys. Lett. 20 (1966) 682; erratum 21 (1966) 720 ($A_2^{(4)}$; AHKN ref.
   [26]).
5. For Stage 1b: S. Laporta, Nuovo Cim. A 106 (1993) 675, and M. A. Samuel, G. Li, Phys.
   Rev. D 44 (1991) 3935 with errata D 46 (1992) 4782 and D 48 (1993) 1879.
6. For Stages 3–5:
   - Mignaco–Remiddi 1969 (set (a));
   - G. Källén, A. Sabry, Dan. Mat. Fys. Medd. 29 (1955) no. 17;
   - Barbieri–Remiddi 1974 and Barbieri–Caffo–Remiddi, Phys. Lett. B 57 (1975) 460 (set (c));
   - S. Laporta, E. Remiddi, Phys. Lett. B 265 (1991) 182 (set (d));
   - Levine–Remiddi–Roskies, Phys. Rev. D 20 (1979) 2068, and S. Laporta, E. Remiddi, Phys.
     Lett. B 379 (1996) 283 (set (e) and the total);
   - T. Kinoshita, Phys. Rev. Lett. 75 (1995) 4728 (numerical check);
   - if the quadrature track is pursued, S. Volkov, arXiv:1507.06435 (three-loop
     subtraction without residual renormalization).
7. Phase 6 inputs: the CODATA 2022 mass ratios (AKN uses
   $m_e/m_\mu=0.483\,633\,170(11)\times10^{-2}$ and $m_e/m_\tau=0.287\,585(19)\times10^{-3}$,
   Table 1).

### 8.2 Risks

- **R1. Meaning of the family predicate.** A predicate can silently drop or double-count
  contractions, for example the `photonCt` slot pairings. Mitigation: O3-4 (predicate ⇔
  orbit), plus an independent audit that counts contractions per class.
- **R2. Fubini at three loops (O3-6).** The two-loop nested VP proof needed a sharper bound
  on the packet-6b spatial integrand; with two subloops the bounds compound. This is the
  main analytic risk of Stage 1. Fallback: prove integrability of the absolute nested
  integrand through the parametric bubble forms (`ParametricBridgeVPFlavour` shapes).
- **R3. Decoupling with products (O3-12).** It is new, though the one-factor version is
  proved; the bound must not need a ratio constraint on $M_2/M_1$.
- **R4. Exact evaluation (O3-13).** Weight 3 with a square-root threshold variable. The
  constants are identified, but the Lean reduction is unwritten. The $n=1$ case took two
  files.
- **R5. Pinning.** The 1969–1978 sources are paywalled scans, as for BMR, and the
  identification of set (b)'s source is open.
- **R6. Scope creep through Q4 and Q5.** A large refactor of the frozen generations would
  delay everything. Keep successors minimal and embedded.
- **R7. Meaningfulness criticism** (the chain is "easy"). Mitigation: report the scope
  exactly, and stage directly to set (c), which reuses the Phase 4 units.
- **R8. High-dimensional certified quadrature may not reach useful precision** for set (d)
  or (e). The pilot (T3) measures this before any commitment.

### 8.3 First bounded tasks

- **T1. Numerical validation of the planned representation** (scripts only; no Lean).
  1. Commit `scripts/numerics/phase5_chains.py`, generalizing the check in section 9.
  2. Add a *model-level* check: evaluate the Stage 1a value at finite
     $(m_\gamma,\Lambda,M_1,M_2)$ from the nested form with $\Pi_{\rm loop}-\delta_3$ (the
     object O3-10 names), not from the already-limited formula. Show convergence to $A_{(b)}$
     in the Q1 order, with the regulator masses last. Also show that the cross terms of
     O3-12 decay without a constraint on $M_2/M_1$.
  3. Reproduce O3-M3 (Pas (10) against the spectral integral) at the mass ratios of AHKN,
     AKN and Pas.

  Acceptance: agreement with every pinned value in section 9 within its stated uncertainty,
  and a regulator table like TWO-LOOP-DERIVATION 11.5. Cost: minutes of single-process CPU.
- **T2. Lean spike on the evaluation risk** (helper level, before any freeze). Prove
  O3-13, $\int_0^1(1-x)\hat\Pi^2=A_{(b)}$, from the explicit $\hat\Pi$. This retires R4 first,
  as `integral_vpUnit` did for O2-18. Estimated 3–8 files.
- **T3. Quadrature pilot** (only when Stage 4 is considered). Certify the X unit's proved 2D
  representation (TWO-LOOP-UNITS (4.4)) by interval quadrature, then a 3D massive-photon
  unit. Record the boxes, kernel time and memory against the precision reached. The
  measurement decides whether 7–8D for set (d) is plausible.

Then send the author the questions Q1–Q8 with the T1 results, before drafting any
declaration.

## 9. Numerical record

Planning scripts (`chain_checks.py`, `tau_check.py`, `ratio_check.py`, `three_pslq.py`; to be
committed as `scripts/numerics/phase5_chains.py` under task T1), `mpmath` at 30–60 digits, tanh-sinh quadrature,
single process, niced. The output is saved alongside in `numerics-run.txt`. This is
evidence, not proof.

| Quantity | Computed | Reference | Status |
| --- | --- | --- | --- |
| one electron bubble, $\int(1-x)\hat\Pi$ | $0.015\,687\,421\,859\,102\,682\,610\,725\ldots$ | $119/36-\pi^2/3$ (BMR-II (1.10); `integral_vpUnit`) | agrees to 30 digits |
| $A_2^{(4)}$, $m_e/m_\mu=4.836\,331\,67\times10^{-3}$ | $5.197\,386\,696\,96\times10^{-7}$ (spectral integral and Pas (10) agree to 15 digits) | Pas (11) $5.197\,386\,70(28)\times10^{-7}$ | agrees |
| same, AHKN ratio $4.836\,331\,66\times10^{-3}$ | $5.197\,386\,675\times10^{-7}$ | AHKN (2.6) $5.197\,386\,67(26)\times10^{-7}$ | agrees |
| same, AKN ratio $4.836\,331\,70\times10^{-3}$ | $5.197\,386\,761\times10^{-7}$ | AKN Table 1 $0.519\,738\,676(24)\times10^{-6}$ | agrees |
| $A_2^{(4)}(m_e/m_\tau)$, Pas, AHKN and AKN ratios | $1.837\,622\,6$, $1.837\,980\,5$, $1.837\,891\,0$ ($\times10^{-9}$) | Pas (12) $1.837\,62(60)$, AHKN (2.7) $1.837\,98(34)$, AKN $1.837\,90(25)$ | agree. Pas (10) needs about 50 digits at $x\approx3477$ because of cancellations. |
| $A_3^{(6)}$, $2\int(1-x)\hat\Pi_\mu\hat\Pi_\tau$ | $1.909\,446\times10^{-13}$ | Pas (21) $1.909\,45(62)\times10^{-13}$ | agrees |
| set (b), $\int(1-x)\hat\Pi^2$ | $0.002\,558\,524\,936\,517\,345\,199\,267\,462\,799\,635\ldots$ | — | equals $(8/3)\zeta(3)-(4/135)\pi^2-943/324$ to $1.3\times10^{-51}$ (PSLQ, then residual) |
| eighth-order I(a), $\int(1-x)\hat\Pi^3$ | $0.000\,876\,865\,858\,889\,990\,697\,9\ldots$ | AHKN Table 1 $0.000\,876\,865\cdots$ | agrees; equals $151849/40824+(32/63)\zeta(3)-(2/45)\pi^4$ to $1.6\times10^{-59}$ |
| tenth-order I(a), $\int(1-x)\hat\Pi^4$ | $0.000\,470\,905\,716$ | AHKN Table 2 $0.000\,470\,94(6)$ | $0.6\sigma$ |
| $e\mu$ chain, $2\int(1-x)\hat\Pi_e\hat\Pi_\mu$ | $2.634\,672\times10^{-7}$ | part of Pas (15) | no pinned comparison |

Conventions: $\hat\Pi_M(s)=\tfrac13\bigl[-\tfrac53+a+(1-\tfrac a2)\beta\ln\tfrac{(\beta+1)^2}{a}\bigr]$,
with $a=4M^2/s$ and $\beta=\sqrt{1+a}$. Its Taylor series is used for $s/M^2<0.1$. It is
checked against the defining integral to $10^{-30}$.

## 10. Task T1 results (2026-11-18)

Script `scripts/numerics/phase5_chains.py` (record `scripts/numerics/phase5_chains.out`; about
200 s on one core). Evidence, not proof.

- **Section 9 reproduced.** Every row agrees with its pinned reference:
  - $A_2^{(4)}(m_e/m_\mu)$ and $A_2^{(4)}(m_e/m_\tau)$ at the Pas, AHKN and AKN mass ratios, all
    within $0.04\sigma$;
  - $A_3^{(6)}$ against Pas (21), AHKN and AKN, within $0.8\sigma$;
  - tenth-order I(a) at $0.57\sigma$;
  - O3-M3: Pas (10) against the spectral integral, to $10^{-29}$ relative.
- **Set (b) at finite regulators** (model level, the object of O3-10): the outer functional of
  $(\Pi_{\rm loop}-\delta_3)^2$ with $\delta_3$ from (Z₈), taken in the Q1 order, regulator
  masses last.
  - It converges to $A_{(b)}$.
  - At fixed regulator masses, the remainders in $m_\gamma$ and in $1/\Lambda$ carry no logarithm.
  - The remaining offset is $\kappa(M_1^{-2}+M_2^{-2})$ with $\kappa=-\tfrac{2}{15}\int x^2\hat\Pi_e$. It
    has no logarithm and does not depend on $M_2/M_1$.
  - The four contraction types each grow like $\ln^2M$ and cancel to the nested value.
- **O3-12.** Both cross terms decay with no constraint on $M_2/M_1$; ratios tried from
  $1+10^{-6}$ to $10^3$.
- **Stage 0 analogue.** The heavy lepton's own VP unit, with its own Pauli–Villars pair,
  converges to Pas (10). The regulators must lie far above $m_\ell$: at $M=(2,3)\,m_\ell$ the value
  shifts by $-33\%$. The bound has the form of `abs_vpLimSum_sub_le`, which is proved only for
  loop mass 1.
- **One discrepancy (candidate finding, not an erratum).** AHKN Table 1, eighth-order I(a), the
  $A_2^{(8)}(m_e/m_\tau)$ entry: at AHKN's own stated ratio $2.87592\times10^{-4}$ the chain
  integral gives $8.024665\times10^{-10}$ against $8.0233(5)\times10^{-10}$, which is $2.7\sigma$.
  At Passera's ratio the difference is $0.4\sigma$. The table entry was probably computed with
  an older tau ratio; this is unconfirmed.
- **Not tested** (as at two loops): the energy-first prescription and $\varepsilon\to0$, the
  $q^2\to0$ limit, nested-equals-joint (O3-6), covariance (O3-8), and the family enumeration
  (O3-3, O3-4).

**Task T2 is done.** O3-13 and O3-14 are proved at helper level (`QED/Chain/`).

**O3-M3 is done** (helper level, `QED/Chain/HeavyLepton*.lean`, `scripts/numerics/chain/heavy_lepton.py`):
- `integral_heavy`: $\int_0^1(1-x)\hat\Pi(y^2x^2/(1-x))\,dx$ equals Passera (10) at $x=1/y$, rewritten with
  dilogarithms of arguments in $(-1,1)$ (`a2Heavy`), for $y\in(0,1)$, with integrability;
- the limits $y\to0^+$ (with $0\le A(y)\le y^2/45$) and $y\to1^-$ ($119/36-\pi^2/3$);
- monotonicity;
- certified enclosures on the AKN Table 1 mass-ratio intervals: $5.197386525\ldots5.197386998\times10^{-7}$ (muon)
  and $1.8376481\ldots1.8381339\times10^{-9}$ (tau).

**O3-M2, analytic core, is done** (helper level, `QED/Chain/HeavyVP*.lean`):
- the heavy-lepton outer functional at loop mass $M_L$ and its joint $(m_\gamma,\Lambda)$ limit;
- decoupling of the heavy lepton's regulators,
  $|\text{PV sum}-\hat\Pi\text{-value}|\le(M_1^{-2}+M_2^{-2})/45$ for $M_1,M_2\ge M_L$, with no
  constraint on $M_2/M_1$ (`abs_heavyLimSum_sub_le`; the constant is numerically sharp);
- the limit value `a2Heavy` (`vpLim_eq_a2Heavy`);
- the split of the outer functional into lepton blocks (`outerF2_blocks`);
- the iterated limit in physical units (`heavyUnitReg_iterated_limit_mass`).

The model-level steps remain: the nested form of the heavy VP class, the flavour-summed photon
condition, model mass scaling, and the assembly of (HM₂).

**O3-10 to O3-12, analytic core for set (b), done** (helper level, `QED/Chain/ChainB*.lean`):
- **O3-10.** The finite-regulator two-bubble outer functional: $64\pi^6$ times the outer
  functional of $(\Pi-\Pi(0))^2s^2D^3$ equals $e^4$ times the explicit chain integral. This holds
  both for any flavour family and for the frozen `Params` (`chainModel_eq_chainReg`).
- **O3-11.** Its joint $(m_\gamma,\Lambda)$ limit.
- **O3-12.** Decoupling in the product:
  $-K(M_1^{-2}+M_2^{-2})\le\text{chainLim}-A_{(b)}\le0$ with $K=(41-4\pi^2)/135=|\kappa|$
  (`chainLim_sub_bounds`), sharp, with no constraint on $M_2/M_1$.
- **The value.** $\int_0^1x^2\hat\Pi=41/18-2\pi^2/9$.
- **The iterated limit** in the D-37 order (`chainReg_iterated_limit`).

The model-level steps O3-3 to O3-9 and O3-15 follow the Stage 1a packet.

**(HC₃) reduced to five named obligations** (`QED/ChainProof/HC*.lean`, conditional helpers):
- **O3-15 is proved.** The assembly in the D-37 order, with the regulator limits and the existence
  clause, goes from a fixed-regulator link (`..._of_fixedLink`).
- **Proved reductions:**
  - the fixed link from four links: ε-limit existence, covariance, mirror, and a one-variable
    q² → 0⁺ value;
  - O3-9 reduced to one variable through covariance (`HCKinematics`);
  - from the class decomposition to the whole vertex (`HCClasses`);
  - the measure-theoretic step of O3-6 at three loops (`HCNestedFubini`), in a direct form and an
    inner-first form.
- **Open:**
  - `ChainClassDecomposition` (O3-4);
  - `ClassLimitLink`, the per-class ε → 0⁺ limits (O3-5/O3-6);
  - `ClassCovLink` (O3-8);
  - `ChainMirrorLink` (O3-8; it holds for the sum only, since C swaps bubble–δ₃ with δ₃–bubble);
  - `ChainPauliAtLink` (O3-9 value, O3-7, O3-10, with mass and charge scaling).
- **Finding on O3-6.** The direct Fubini route needs a bubble bound with exponent below 13/2, but
  the proved two-loop bound gives 17/2. The inner-first route integrates the first bubble in closed
  form (`VPHalfAtInner`), which reduces the rest to the two-loop VP shape, where 17/2 appears to
  suffice.

**O3-4 is done** (`QED/ChainProof/Enum*.lean`):
- Every set (b) contraction is a relabelling of exactly one of 9 representatives. The
  classification comes from the path argument; no permutations are enumerated.
- No representative has a nontrivial automorphism, so each class has coefficient one.
- `vertexChain_two_eq_classes_flavors` gives the chain vertex as the signed sum of the 9
  representative values, for every flavour set.
- The (C₁) implications are proved at n = 2: 1PI, order 7, loop count 1 + #bubbles, sign
  (−1)^#bubbles.

(HC₀) is reduced to integrability of the 9 representatives
(`jointEnergyFirstIntegrable_vertexChain_two_of_reps`). That needs criteria the repository does not
yet have: three loop momenta, and numerators of degree 6, because the `photonCt` factor is quadratic.

**The value link, reduced** (`QED/ChainProof/HCValue*.lean`):
- the q² → 0⁺ step for the one-loop outer functional;
- the set (b) photon function (Π_loop − δ₃)² s² D³ and its limit;
- its value e⁶·chainRegMass/(64π⁶), with mass scaling and δ₃ from (Z₈);
- the counterterm combination O3-7 on the nine enumerated classes (`enumPhoton_sum`);
- `chainPauliAtLink_of_enum`.

The open input, `ClassNestedAtLink enumClass enumPhoton`, is O3-6 per class at fixed q: each class
limit is the one-loop vertex with its inserted photon function. It is the same work as
`ClassLimitLink`.

**Covariance and mirror** (`QED/ChainProof/HCCov*.lean`):
- **The mirror link is proved** from existence and covariance alone. The fixed-ε identity
  `chainMirrorAt` is proved unconditionally, by reversing every momentum and applying charge
  conjugation to the whole family sum, which swaps the bubble–δ₃ and δ₃–bubble classes.
- **(HC₃) now needs three links:** the per-class ε-limits, the per-class covariance and the value
  link (`isFormFactorPair_vertexChain_two_pauli_limit_of_classLinks`). `enumClass_eq_chainClassX`
  identifies the class families used by the value and covariance links.
- **Per-class covariance under boosts is not a fixed-ε symmetry** of the energy-first integral. It
  must be read off the closed form of the ε → 0⁺ limits (O3-6), as at two loops.

**Per-class limits, part 1** (`QED/ChainProof/HCLimit*.lean`):
- `ClassLimitLink enumClass` is reduced to the nine representatives.
- The four δ₃–δ₃ classes have ε → 0⁺ limits with no hypotheses. Their value does not depend on the
  field pairing, which confirms the δ₃²/4 split in `enumPhoton`.
- The bubble–bubble Fubini step is proved (risk R2): joint equals nested
  ∫ O(k)·Π_ε(k)², with new bounds on the unintegrated and integrated bubbles. The decay exponent
  14 is exactly enough.

Open:
- the bubble–bubble Wick step, matching the representative's amplitude to the nested integrand;
- the ε → 0⁺ limits for bubble–bubble, bubble–δ₃ and δ₃–bubble (numerators beyond quadratic);
- the per-class closed forms, which give `ClassNestedAtLink` and `ClassCovLink`.

**Per-class limits, part 2** (`QED/ChainProof/HCSide*.lean`):
- **The δ₃–δ₃ classes are done:** limit, closed form (`classLimit_repDD_eq`), nested value with the
  δ₃²/4 coefficient proved, and covariance.
- **The three links reduce to 15 inputs** (`classLinks_of_reps`): `RepLimit`, `RepNested` and
  `RepCov` for `repBB`, `repBD s` and `repDB s`.
- **The side classes are reduced algebraically** (`HCSideBDAlgebra`). Their Pauli projection is
  −(i/2)δ₃ k²d(k) times the VP class's. Two pieces of work remain:
  - the VP assembly engine, which is written for photon masses (a,b,a,b), must be generalized to
    extra photon lines;
  - the parametric route for the full matrix limit must be extended to 11- and 12-line shapes.

**Bubble–bubble, part 1** (`QED/ChainProof/HCBB*.lean`):
- **The Wick step is proved.** The value of `repBB` is the three-loop joint integral of
  `bbIntegrand` with the outer factor `chainOuter`, whose constants are confirmed. Given
  integrability, it is the one-loop vertex integral with the double insertion
  d³(Π̂_ε²k²(k²g − kk) − ε(…)).
- **The limit, nested value and covariance are reduced** to statements about that integral.
- **The analytic core remains:** the ε → 0⁺ limit with several different iε prescriptions, one
  from each spectral bubble plus ε itself. It needs a dominated-convergence engine for mixed
  prescriptions with more photon-type powers. The side classes need the same engine.

**Integrability (HC₀)** (`QED/ChainProof/RepsInt*.lean`):
- **Eight of the nine representatives are proved integrable at ε > 0:**
  - δ₃–δ₃, without the Pauli–Villars conditions;
  - bubble–δ₃ and δ₃–bubble, through the loop's Ward identity and the two-loop refined criterion.
- **(HC₀) is reduced to one hypothesis,** integrability of `repBB`
  (`jointEnergyFirstIntegrable_vertexChain_two'_of_remaining`).
- **The gap is a three-loop numerator-aware criterion:** Symanzik with 3×3 minors, the
  three-dimensional energy integral, a spatial bound on ℝ⁹, and the Fubini steps. It is comparable
  to the existing two-loop machinery. The outer energy integral must stay signed, because absolute
  values destroy the gauge cancellation.
