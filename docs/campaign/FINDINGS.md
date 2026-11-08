# Findings ledger

[Campaign HQ](../../README.md) · [Status](STATUS.md) · [Decisions](DECISIONS.md) ·
[Sources](../SOURCES.md)

This ledger records source gaps, convention differences, and candidate errors,
each with exact evidence and a review status. A candidate source error is
recorded with its pinned location and quoted text. It becomes an established
erratum only after it has been checked against the pinned bytes by someone
other than the person who found it. The project's own corrections and proof
obligations are listed as such; they are not errata.

Locations refer to the pinned bytes in [SOURCES.md](../SOURCES.md). "p." means
the PDF page.

**Status values**

| Value | Meaning |
| --- | --- |
| `open` | recorded, not yet independently checked |
| `verified` | independently checked against the pinned bytes |
| `resolved` | handled by a decision or a proof |
| `withdrawn` | no longer stands |

| ID | Kind | Summary | Status |
| --- | --- | --- | --- |
| F-1 | Gap in the standard treatment | A Feynman-$i\epsilon$ Minkowski loop integral is not a Lebesgue integral over $\mathbb R^4$ | resolved by D-5 (prescription M1); independent review pending |
| F-2 | Deliberate deviation | The project regulates the UV with Pauli–Villars; the primary source uses dimensional regularization | resolved by D-5 |
| F-3 | Source erratum | `srednicki-draft` (56.6): $e^{ikx}$ should be $e^{-ikx}$ | verified |
| F-4 | Source erratum | `srednicki-draft` (63.6): missing "+" before the final $m$ | verified |
| F-5 | Source erratum | `srednicki-draft` p. 380: "$p^2=-p'^2=-m^2$" should be "$p^2=p'^2=-m^2$" | verified |
| F-6 | Source erratum | `srednicki-draft` (63.21): denominator sign | verified |
| F-7 | Source gaps | Steps the primary source leaves to exercises or to "the usual manipulations" | open; each gap is a project obligation |
| F-8 | Modeling gap | The source's magnetic-moment argument passes through an asserted quantum action | open; handled by D-9 (both definitions, no inserted form-factor values) and obligations O-21 and O-24 |
| F-9 | Secondary-source misprints | `kaplunovsky-vertex` K(25) index and "q² = 1" on p. 8 | verified |
| F-10 | Candidate normalization issue | `ahkn-2012` projector (4.4) returns $F_2/m$; it is correct only in units $m=1$ | open |
| F-11 | Candidate source misprint | `srednicki-draft` p. 383: wave-packet width "$a\ll1/m$" should apparently be $a\gg1/m$ | open; needs an independent check |
| F-12 | Process gap | Packet 1's frozen definitions depend on infrastructure definitions whose bodies were not shown to the author and are not frozen | open; packet 1b proposed |

## F-1. Minkowski loop integrals are not absolutely convergent

**Kind.** A gap in the standard textbook treatment, including the primary
source's informal Wick rotation (14.16), p. 112. It is not an erratum of a
specific equation.

**Claim.** Let $D>0$, $\epsilon>0$, and $n\ge1$. Then
$\ell\mapsto\bigl(-(\ell^0)^2+|\vec\ell|^2+D-i\epsilon\bigr)^{-n}$ is not Lebesgue
integrable on $\mathbb R^4$. This holds even when the integrand converges by
Euclidean power counting. Steps that treat the loop integral as an ordinary
integral over $\mathbb R^4$ (Fubini, shifts, contour rotation) are therefore
unjustified as stated.

**Argument.** Fix $\rho=|\vec\ell|$ and set $\omega^2=\rho^2+D$. Near
$\ell^0=\pm\omega$ the denominator is about $\mp2\omega(\ell^0\mp\omega)-i\epsilon$,
so
$$\int_{\mathbb R}\frac{d\ell^0}{|-(\ell^0)^2+\omega^2-i\epsilon|^{n}}\ \ge\
\frac{c_n}{\omega\,\epsilon^{n-1}}\qquad(\rho\ \text{large}),$$
and $\int_{\mathbb R^3}d^3\ell\,\omega^{-1}=4\pi\int\rho^2\omega^{-1}d\rho=\infty$.

**Evidence.** For $n=3$, $\epsilon=0.1$, and $D=1$,
[`scripts/numerics/one_loop_sanity.py`](../../scripts/numerics/one_loop_sanity.py)
(check 7) gives the energy integral of the absolute value as $141.8$, $19.90$,
$2.000$, and $0.2000$ at $\rho=1,10,10^2,10^3$. That is about $200/\rho$, so
$\rho^2$ times it grows linearly. This floating-point evidence supports the
analytic argument; it is not a proof.

**Resolution.** Decision D-5 adopts prescription M1 (energy integral first, then
$\epsilon\to0^+$) as the definition of the Minkowski loop integral for the
pilot. The justification steps become obligations O-6, O-7, O-9, and O-10 of
the [derivation](../ONE-LOOP-DERIVATION.md).

## F-2. Pauli–Villars instead of dimensional regularization

**Kind.** A deliberate deviation from the primary source.

**Evidence.** The source continues to $d=4-\varepsilon$ for the UV (pp. 371–376;
(62.47)–(62.49)) and uses a photon mass for the IR ((62.29), p. 374). It takes
$\varepsilon\to0$ before extracting the form factors (p. 380) and sets
$m_\gamma=0$ in $F_2$ (p. 382).

**Project choice.** Decision D-5 uses a Pauli–Villars photon of mass $\Lambda$
together with the photon mass $m_\gamma$. The finite parts of $Z_1$, $Z_2$, and
the source's $\kappa_1$, $\kappa_2$ therefore differ from the source. $F_2$
reproduces (63.20) plus a term bounded by $m^2/(3\Lambda^2)$ at $q^2=0$
([REGULARIZATION.md, section 6](../REGULARIZATION.md#6-regulator-dependence-of-the-target-and-bounded-feasibility)).
That agreement is part of obligation O-16. Review statements against the source
must account for this deviation explicitly.

The source itself names Pauli–Villars regularization as an alternative in its
scalar example, (14.22), p. 114, and says the final result is the same there.

## F-3 to F-6. Misprints in the primary source

The source worker found each of these in the pinned draft. The orchestrator then
checked each against the pinned bytes, and each also appears in the author's
published errata list. The author's list uses the published edition's
pagination; the draft page is given here. The errata page was snapshotted
during source selection; it is not committed.

| ID | Location (draft) | Printed text | Correction | Independent evidence |
| --- | --- | --- | --- | --- |
| F-3 | (56.6), p. 339 | $\langle k,\lambda\vert A^i(x)\vert0\rangle=\varepsilon^i_\lambda(k)e^{ikx}$ | $e^{-ikx}$ | Author's errata ("p.344, eq.(56.6), e^ikx should be e^-ikx") |
| F-4 | (63.6), p. 379 | "$[-(1-x_1)\not p+x_2\not p'\ m]$" | "$+\,m$" | Inconsistent with (62.46) on p. 376, which has "$+x_2\not p'+m$"; author's errata ("p.387, eq.(63.6), there should be a plus sign in front of the final m") |
| F-5 | p. 380, last paragraph | "with $p^2=-p'^2=-m^2$" | $p^2=p'^2=-m^2$ | Contradicts the on-shell conditions used throughout chapter 63; author's errata ("p.388 ... $-p'^2$ should be $+p'^2$") |
| F-6 | (63.21), p. 382 | denominator "$1-y(1-y)q^2/m^2$" | $1+y(1-y)q^2/m^2$ | Substituting $x_1=(1-x_3)y$ into (63.20) gives $x_1x_2q^2/m^2+(1-x_3)^2=(1-x_3)^2[1+y(1-y)q^2/m^2]$ (orchestrator derivation). At $q^2/m^2=0.7$, (63.20) gives $0.8975456$, which matches the corrected form; the printed form gives $1.1359$ (source worker's numerical check). Author's errata ("p.389, eq.(63.21), 1-y(1-y)... should be 1+y(1-y)") |

None of these changes $F_2(0)=\alpha/2\pi$. F-4 and F-6 sit inside the chain the
project formalizes, so the derivation uses the corrected forms.

## F-7. Steps the primary source leaves out

Each item is a project obligation in the [derivation](../ONE-LOOP-DERIVATION.md),
not a defect of the source:

| Location | What is skipped | Obligation |
| --- | --- | --- |
| (14.9)–(14.11), problem 14.1 | proof of Feynman's formula | O-5 |
| (14.16), p. 112 | Wick rotation, argued informally | O-7 (via F-1) |
| (14.27) | master integral, stated without derivation | O-11 |
| (62.18), problem 14.3 | symmetric integration | O-9 |
| p. 376 | "terms linear in $q$ integrate to zero"; "Performing the usual manipulations" (62.49) | O-9, O-11 |
| (63.10), problem 47.2 | contraction identities | O-4 |
| (63.13) | on-shell reduction, stated rather than displayed | O-12 |
| (63.16), problem 38.4 | Gordon identity, derivation sketched | O-14 |
| problem 63.1 | general vertex structure and current conservation | O-15 (existence obtained from the explicit computation instead) |
| p. 373 / (62.29) | Feynman gauge with a massive photon, not justified | [REGULARIZATION.md, section 3](../REGULARIZATION.md#3-the-regulated-model-ingredients) |

## F-8. The magnetic-moment step passes through an asserted quantum action

**Kind.** A modeling gap in the primary source's observable step.

**Evidence.** On p. 383, "Eq. (64.1) follows from a quantum action of the form"
(64.3) is asserted. On p. 384, "we define the interaction hamiltonian as what we
get from the two displayed terms in eq. (64.3)" (64.6). The magnetic moment is
then defined by $\mu B\equiv-\langle e|H_1|e\rangle$ (64.7), and its evaluation
(64.8)–(64.15) uses $H_1$, not the vertex function directly.

**Consequence.** Linking the vertex function to the measured magnetic moment
requires a proof that the static-field response is given by the vertex at
$q\to0$ (obligation O-21). Ruling D-9 adopts both the source's definition and
the vertex-response definition, to be proved equivalent (O-24). The project's
version of the source definition must obtain the matrix elements of $H_1$ from
the model's current matrix elements. Inserting $F_1(0)$ and $F_2(0)$ as (64.6)
does would make the equivalence circular. See
[ONE-LOOP-DERIVATION.md, stage 5](../ONE-LOOP-DERIVATION.md#stage-5--magnetic-interpretation).

## F-9. Misprints in the secondary source

`kaplunovsky-vertex`:

- K(25), p. 6, prints the Gordon identity as "$(p'+p)^\mu\cong2m\gamma^\mu-i\sigma^{\mu\nu}q_\mu$".
  The index on $q$ should be $\nu$.
- p. 8 reads "The electric form factor $F_1\equiv F_{el}$ for $q^2=1$ is
  constrained by the Ward identity". The context requires $q^2=0$.

The source worker found both, and the orchestrator confirmed them in the pinned
bytes. They do not affect any result the project uses.

## F-10. Possible normalization of the AHKN magnetic projector

**Claim (open, from source selection).** As printed, the projector (4.4) of
`ahkn-2012`, p. 12, gives $\mathrm{Tr}(P_\nu\Gamma^\nu)=F_2/m$, so it yields $F_2$
only in units $m=1$. The paper appears to use such units implicitly (cf. (7.2),
p. 31), but no explicit statement was found. The source worker checked this
numerically. Nobody else has checked it, and the project does not currently
rely on this projector.

## F-11. Wave-packet width condition in the magnetic-moment chapter

**Claim (candidate).** On p. 383, after (64.5), the source says that the wave
packet $f(\mathbf p)\sim\exp(-a^2\mathbf p^2/2)$ is "sharply peaked at
$\mathbf p=0$" and gives the condition "with $a\ll1/m$". The orchestrator
confirmed this text on the rendered page. The momentum spread of this packet
is of order $1/a$. Being sharply peaked relative to $m$, which is what the
linear-order expansion "since the wave packet is sharply peaked at
$\mathbf p=0$" (pp. 384–385) needs, means $1/a\ll m$, that is $a\gg1/m$: a
packet spatially larger than the Compton wavelength. No entry for chapter 64
was found in the snapshot of the author's errata list taken during source
selection.

**Status.** Open. The orchestrator found it and has not had it independently
checked. It matters because D-9 requires the formal source definition of $\mu$
to state the limit of sharply peaked packets explicitly.

## F-12. Infrastructure definitions in packet 1's closure were not shown or frozen

**Kind.** Process gap, found by the orchestrator while freezing packet 1. It is
not a source issue.

**Evidence.** The frozen definitions use these infrastructure definitions:

- (A) `electronPropagator` uses `QED.Minkowski.dot` and `QED.Dirac.slash`;
- (B) `photonPropagator` uses `QED.Minkowski.metric` and `QED.Minkowski.dot`;
- (C) `vertexIntegrand` uses `QED.Dirac.gamma`;
- `slash` uses `QED.Minkowski.lower`, which uses `metric`.

These definitions carry meaning and are committed with proved properties
(Clifford relation, `dot_eq`, `lower_eq`). But their bodies were not displayed
in the packet-1 review, and they live in ordinary modules. The frozen-anchor
guard therefore does not detect a change to them, which would silently change
the meaning of (A)–(C) and (E). The skill requires the author to see "a
definition's whole body" for meaning-carrying definitions.

**Resolution (proposed).** Packet 1b shows the exact committed bodies of
`metric`, `dot`, `lower`, `gamma`, and `slash` for approval. It then moves each
into its own frozen file with unchanged export names, so the bytes of (A)–(E)
and their ABI hashes stay the same, and adds the files to the closures. Until
then, no change to those five definitions may land.
