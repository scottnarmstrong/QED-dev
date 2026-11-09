# Decision log

[Campaign HQ](../../README.md) · [Status](STATUS.md) · [Findings](FINDINGS.md)

Decisions actually made, with reasons and scope. Author rulings are marked as
such. A decision about the mathematical route is not approval of any Lean
declaration: only exact Lean declarations can be approved and frozen.

| ID | Date | Decision | Made by |
| --- | --- | --- | --- |
| D-1 | 2026-11-07 | Repository made public | Author |
| D-2 | 2026-11-07 | Source bytes are pinned by hash and kept in an untracked local cache | Orchestrator |
| D-3 | 2026-11-07 | Pin Lean `v4.35.0` and Mathlib `v4.35.0` | Orchestrator |
| D-4 | 2026-11-07 | One Lake package `qed` with library `QED` | Orchestrator |
| D-5 | 2026-11-07 | One-loop pilot route: Pauli–Villars photon, photon mass, Feynman gauge, on-shell scheme, energy-first Minkowski integral | Orchestrator |
| D-6 | 2026-11-07 | Primary source: Srednicki's draft, chs. 58 and 62–64; secondary: Kaplunovsky's vertex notes | Orchestrator |
| D-7 | 2026-11-07 | Adopt the primary source's conventions (mostly-plus metric, Weyl representation, $e<0$) | Orchestrator |
| D-8 | 2026-11-07 | The formal model starts from a momentum-space Wick expansion at order $e^3$ (ruling on P-1) | Author |
| D-9 | 2026-11-07 | Both magnetic-moment definitions, proved equivalent (ruling on P-2) | Author |
| D-10 | 2026-11-07 | The repository is licensed under Apache-2.0 | Author |
| D-11 | 2026-11-08 | Packet 1 (regulated one-loop vertex integrand and its well-definedness) approved as written and frozen | Author |
| D-12 | 2026-11-08 | Packet 1b (the Minkowski and Dirac definitions in packet 1's closure) approved as written and frozen | Author |
| D-13 | 2026-11-08 | Provider binder convention for sealing theorem anchors whose binders precede the colon | Orchestrator |
| D-14 | 2026-11-08 | Packet 2 (one-loop vertex, form-factor decomposition, and the one-loop anomaly headline) approved as written and frozen | Author |
| D-15 | 2026-11-08 | Packet 3 (vertex function, charge condition, counterterm shift, and F₁(0) = 1) approved as written and frozen | Author |
| D-16 | 2026-11-08 | Packet 4a (response magnetic moment and the one-loop Landé factor; spinor definitions) approved as written and frozen | Author |
| D-17 | 2026-11-08 | Design of packet 4b (source definition of the magnetic moment): next milestone; absolute convergence of the position integral; real compact rotationally invariant packets | Author |
| D-18 | 2026-11-08 | Packet 4b (wave-packet current density, source magnetic moment, equivalence O-24, and the source Landé factor) approved as written and frozen | Author |
| D-19 | 2026-11-08 | Design of L1.VERTEX (Wick derivation of the vertex): the 1PI vertex; the full counterterm set; canonical one-loop routing; general contraction combinatorics | Author |
| D-20 | 2026-11-09 | Packet 5 (the Wick derivation of the vertex) approved as written and frozen; the frozen-anchor guard accepts the definitional keywords `abbrev`, `inductive`, `structure` and `instance` | Author; guard change by the orchestrator |
| D-21 | 2026-11-09 | Design of L1.ASSEMBLY: one headline theorem from the Wick vertex; prove both sides of O-3 (residues); fresh-checkout audit, Comparator challenge and errata ledger | Author |
| D-22 | 2026-11-09 | Fermion-loop regulator for the photon side of O-3: Pauli–Villars regulator fermions as new fields of the Wick model | Author |
| D-23 | 2026-11-09 | Design of O-3: the full LSZ amplitude; a general successor of the Wick model with arbitrary external fields and the regulator fermions | Author |
| D-24 | 2026-11-09 | Packet 6a (the general Wick model) approved as written and frozen; the regulator fermions enter as a flavoring summed inside the loop integrand | Author |
| D-25 | 2026-11-09 | The on-shell conditions (62.27) and (62.11) are formalized in the literal covariant form, with the decompositions of Σ and Π proved | Author |
| D-26 | 2026-11-09 | Packet 6b-1 (self-energy and vacuum-polarization existence and covariant forms) approved as written and frozen; regulator masses M₁, M₂ > m | Author |
| D-27 | 2026-11-09 | Packet 6b-2, electron half (self-energy form factors, Σ(p̸), the on-shell conditions (62.27), and the unique δ₂, δ_m) approved as written and frozen | Author |
| D-28 | 2026-11-09 | Packet 6b-2, photon half (the vacuum polarization function, Π(0) = 0 (62.11), and the unique δ₃) approved as written and frozen | Author |
| D-29 | 2026-11-09 | Packet 6c design: background-field photon leg with the vacuum-polarization insertion; iterated LSZ limit along any approach; magnetic moments restated with the LSZ amplitude | Author |
| D-30 | 2026-11-09 | Packet 6c-1 (existence and uniqueness of the LSZ amplitude of the electron current) approved as written and frozen | Author |
| D-31 | 2026-11-09 | Packet 6c-2 (the LSZ amplitude, its closed form, and the charge condition and magnetic moments restated with it) approved as written and frozen | Author |

## Pending author rulings

None open. P-1 was resolved by D-8 and P-2 by D-9; both rulings were made on
2026-11-07.

## D-1. Repository visibility (author ruling)

**Decision.** `scottnarmstrong/QED-dev` was changed from private to public on
2026-11-07, at the author's explicit instruction. The orchestrator launch brief
said not to change visibility during the launch; the author's direct
instruction superseded that line. The author also asked for the collaborator
`jaumededios` to be invited with write access; the invitation was sent the same
day.

**Consequences.** Everything committed is published. Copyrighted source
documents are not committed (D-2). No credentials or private material were
present in the eight tracked files reviewed before the change.

## D-2. Source archive policy

**Decision.** For each pinned source, record the exact URL, retrieval time,
byte size, and SHA-256 in [SOURCES.md](../SOURCES.md). Keep the bytes in an
untracked local cache rather than in Git, unless the source's license permits
redistribution.

**Reason.** The repository is public (D-1), and textbook drafts and journal
PDFs generally may not be redistributed. A hash pins the exact bytes that
reviews compare against while respecting their terms.

## D-3. Lean toolchain and Mathlib pin

**Decision.** `lean-toolchain` is `leanprover/lean4:v4.35.0`. Mathlib is
required at tag `v4.35.0`, which resolves to commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`.

**Reasons.**

- It is the newest stable toolchain installed on the machine. Mathlib at this
  tag is modular, as the campaign's module-system rule requires, and its
  dependencies are reached only through Mathlib.
- Two other campaigns on this machine have complete Mathlib builds at exactly
  this commit. The dependency tree was copied from one of them with a plain
  copy, not hardlinks (ext4 has no copy-on-write). `lake build --no-build` then
  reported Mathlib up to date, so no Mathlib rebuild was needed.
- The Mathlib inventory ([MATHLIB-INVENTORY.md](../MATHLIB-INVENTORY.md)) was
  taken at this commit.

**Scope.** Any later toolchain or Mathlib change is a deliberate decision with
its own entry.

## D-4. Package layout

**Decision.** One Lake package, `qed` (`lakefile.lean`), with default library
`QED` rooted at `QED.lean`. The options are `autoImplicit false` and
`relaxedAutoImplicit false`, plus the standard unused-variable and deprecation
linters.

**Reason.** This is the smallest layout that supports the proposed `QED/...`
module areas of the [outline](../PROJECT-OUTLINE.md). When the first module
under `QED/` lands, the library switches to
`globs := #[.andSubmodules `QED]`, so no module can be left unbuilt. The
frozen-anchor quarantine globs are added when the first anchor exists.

## D-5. Regularization route for the one-loop pilot

**Decision.** Route B of [REGULARIZATION.md](../REGULARIZATION.md):

- a Pauli–Villars regulator of mass $\Lambda$ on the photon propagator for
  the UV, and the source's photon mass $m_\gamma$ (62.29) for the IR;
- Feynman gauge and the source's on-shell renormalization conditions;
- Minkowski loop integrals defined by prescription M1: the energy integral
  first, then the spatial integral, then $\epsilon\to0^+$;
- the order of limits $\epsilon\to0^+$, then on shell with spacelike $q$
  ($q^2>0$ in the mostly-plus metric of D-7), then $q^2\to0^+$, then the
  joint limit $(m_\gamma,\Lambda)\to(0,\infty)$.

**Reasons.** All objects are classical and finite-dimensional. Every
contribution that can affect $F_2$ at order $e^2$ is regulated. The
Ward–Takahashi identity is preserved, and the regulator dependence of the
target is explicit. A plain Feynman-$i\epsilon$ Minkowski integral is not a
Lebesgue integral over $\mathbb R^4$ ([F-1](FINDINGS.md)), so the
energy-first definition is needed.

**Scope.** This applies to the one-loop pilot only; the two-loop phase re-opens
the regulator choice. The deviation from the primary source's dimensional
regularization is recorded as [F-2](FINDINGS.md). The exact Lean definitions implementing D-5 carry meaning
and require author approval before freezing. Zimmermann's absolutely convergent
prescription (M2) is the recorded fallback.

## D-6. Primary and secondary sources

**Decision.** The primary source is M. Srednicki's prepublication draft of
*Quantum Field Theory* (`srednicki-draft`), chapters 58 and 62–64, with the
convention and tool chapters listed in [SOURCES.md](../SOURCES.md). The
secondary source is the Kaplunovsky vertex notes (`kaplunovsky-vertex`),
used for the steps the primary source leaves out. Both are pinned by SHA-256
(D-2).

**Reasons.** Of the seven freely retrievable candidates examined, the primary
source is the only one that covers, in one set of conventions:

- the Lagrangian;
- Feynman rules derived from the path integral;
- LSZ with unit-residue external lines;
- the one-loop vertex;
- the on-shell charge condition;
- the form-factor reduction;
- $F_2(0)=\alpha/2\pi$;
- an explicit definition of the magnetic moment.

Its core algebra was checked numerically, independently of the text. Its known
misprints are on the author's own errata list (F-3 to F-6). The secondary
source displays the parametrization, shift, Wick rotation, symmetric
integration, and on-shell algebra.

**Limits.** The draft cannot be redistributed. Its UV regulator differs from
the project's (F-2). Its magnetic-moment step contains an asserted modeling
step (F-8, P-2).

## D-7. Conventions

**Decision.** Adopt the primary source's conventions: metric
$\mathrm{diag}(-1,+1,+1,+1)$, Weyl-representation gamma matrices with
$\{\gamma^\mu,\gamma^\nu\}=-2g^{\mu\nu}$, $\bar u u=2m$, electron charge $e<0$,
vertex $ie\gamma^\mu$, and the form-factor decomposition (63.18).
[CONVENTIONS.md](../CONVENTIONS.md) records them, with a dictionary to the
mostly-minus convention used by the secondary and background sources.

**Reason.** Source-facing declarations are audited directly against the
primary source. Matching its conventions removes a translation layer from
every statement review. The gamma matrices are numerically identical to those
of the common mostly-minus Weyl convention, and $F_2(0)$ is the same number
in both.

**Scope.** This governs the one-loop pilot's Lean infrastructure. Later phases
that use mostly-minus sources (for example `ahkn-2012`) translate through the
dictionary rather than change the base convention.

## D-8. Where the formal model starts (author ruling on P-1)

**Ruling.** The author approved option 2 of
[ONE-LOOP-DERIVATION.md, stage 0](../ONE-LOOP-DERIVATION.md#stage-0--model-data).
The order-$e^3$ electron–electron–photon function is defined as the finite sum
over Wick contractions of the interaction vertices, with fermionic signs,
using the momentum-space free propagators of the regulated model (D-5).

**Consequences.**

- Obligations O-1 and O-2 (the diagram content and the coefficient and sign of
  the one-loop 1PI diagram) become theorems about that expansion. They are no
  longer modeling statements.
- The pilot needs Wick-contraction and Grassmann-sign infrastructure, which
  Mathlib lacks ([inventory, section 8](../MATHLIB-INVENTORY.md#8-fermionic-and-combinatorial-structures)).
- The path integral (58.17)–(58.21) and position-space time-ordered products
  remain background motivation and are not formalized.

**Scope.** The ruling approves a starting level, not any Lean declaration. The
exact definitions of the expansion are meaning-carrying and go through the
review and approval gate.

## D-9. The magnetic moment: both definitions, proved equivalent (author ruling on P-2)

**Ruling.** The project formalizes both candidate definitions of the magnetic
moment and proves that they agree:

- **Source definition** (`srednicki-draft` (64.4)–(64.7)): $\mu B\equiv-\langle e|H_1|e\rangle$.
  Here $|e\rangle$ is a normalized, rotationally invariant one-electron wave
  packet at rest with spin up along $\vec B$, and $H_1$ is the linear-in-$B$
  interaction with the constant field $A=(0,Bx,0)$.
- **Response definition**: the zero-recoil magnetic response of the vertex
  function, read off from the spin-dependent, linear-in-$q$ part of the
  static-field matrix element (obligation O-22).
- **Equivalence theorem**: the two definitions give the same $\mu$ (obligation
  O-24 of the [derivation](../ONE-LOOP-DERIVATION.md#stage-5--magnetic-interpretation)).
  Together with $\mu=\frac{e}{2m}[F_1(0)+F_2(0)]$ (O-21, O-22), this gives
  $g=2[1+F_2(0)]$.

**Design constraints that follow.**

1. *No circularity.* The source writes $H_1$ in (64.6) with the computed
   form-factor values already inserted, via the asserted quantum action (64.3)
   (F-8). If the project's source definition were built the same way, the
   equivalence would hold by construction. Instead, the one-electron matrix
   elements of $H_1$ must come from the model. They are the matrix elements of
   the electromagnetic current at the computed order, related to $V^\mu$ through
   the LSZ and amputation convention of O-3. The values $F_1(0)$ and $F_2(0)$
   must not be inserted.
2. *The wave-packet limit must be explicit.* The expectation value in (64.7)
   depends on the packet. The source expands to linear order "since the wave
   packet is sharply peaked at $\mathbf p=0$" (pp. 384–385). The formal
   definition must state the limit of sharply peaked packets, with its order
   relative to the regulator limits. The source's stated width condition
   appears to be misprinted (candidate finding F-11).
3. *Constant field.* The vector potential $A=(0,Bx,0)$ does not decay. The
   source handles the factor $x$ by differentiating in momentum and integrating
   by parts against the packet ((64.9)–(64.10)). This needs the current matrix
   element to be differentiable in the momenta near $\mathbf p=\mathbf p'=0$,
   not merely continuous in $q^2$.
4. *Infrastructure.* The source definition needs one-particle states with the
   normalization (41.5), wave packets, and the one-particle matrix elements of
   the current. These are new infrastructure.

**Scope.** As with D-8, the exact definitions and the equivalence statement go
through the review and approval gate.

## D-10. License (author ruling)

**Ruling.** The repository is licensed under the Apache License, Version 2.0.
`LICENSE` holds the unmodified Apache-2.0 text, the same file Mathlib ships
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`).
Lean files carry the Mathlib-style header line "Released under Apache 2.0
license as described in the file LICENSE."

**Scope.** The license covers the project's own files. It does not cover the
third-party source documents listed in [SOURCES.md](../SOURCES.md). Their bytes
are not committed, and their own terms apply (D-2).

## D-11. Packet 1 approved (author ruling)

**Ruling.** On 2026-11-08 the author approved packet 1 "as written". The
approved text was the complete Lean source shown to the author, five
declarations with their imports and docstrings, in an untracked scratch file
with SHA-256 `86b49730af675b5e83913e14ff4139649f6ea9180c40e3eff5e092819b6b44de`.
Before approval, an independent refute-first reviewer had checked the
declarations against rule 9, (62.12), (62.29), and (62.40), together with
decision D-5. The review found no blockers and no errors and judged (E) true.
Its one weak finding and four nits were applied to the text the author saw.

**Frozen anchors** (bound by [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json)):

| Anchor | Export | Kind and state |
| --- | --- | --- |
| (A) `QED/Frozen/OneLoop/ElectronPropagator.lean` | `QED.OneLoop.electronPropagator` | definition, `SEALED` |
| (B) `QED/Frozen/OneLoop/PhotonPropagator.lean` | `QED.OneLoop.photonPropagator` | definition, `SEALED` |
| (C) `QED/Frozen/OneLoop/VertexIntegrand.lean` | `QED.OneLoop.vertexIntegrand` | definition, `SEALED` |
| (D) `QED/Frozen/OneLoop/EnergyFirstIntegral.lean` | `QED.OneLoop.energyFirstIntegral` | definition, `SEALED` |
| (E) `QED/Frozen/OneLoop/VertexLimitExists.lean` | `QED.OneLoop.vertexLimit_existsUnique` | theorem, `DRAFT_SORRY`, quarantined; provider `QED.Provider.OneLoop.vertexLimit_existsUnique` |

**Packaging, as announced in the packet.**

- Each declaration is the only public declaration of its own module file.
- Each file imports what it needs. File (C) imports
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` for `Real.pi`; the
  combined packet file had obtained it transitively.
- The proof body of (E) is placed between the guard's marker comments as
  `by sorry`.

A script confirmed that every docstring and declaration is byte-identical to
the approved text, apart from that marker placement.

**Guards.**

- [`scripts/check_frozen_anchors.py`](../../scripts/check_frozen_anchors.py)
  is a verbatim copy of the lean-orchestrator skill's checker. It checks:
  - file, prefix, and suffix hashes;
  - definition-closure hashes;
  - one declaration per file;
  - the module header;
  - that the `DRAFT_SORRY` body is exactly `by sorry`;
  - that nothing outside the allowlists imports or names the draft anchor or
    its provider;
  - that there are no other `sorry`s and no `axiom`s.
- [`scripts/frozen_abi.py`](../../scripts/frozen_abi.py) recomputes the
  elaborated ABI hashes. It uses `pp.all` printing: type and body for
  definitions, statement only for theorems.
- The guard was shown to reject five violations:
  - an edited frozen statement;
  - an edited definition body;
  - an unregistered `sorry`;
  - an import of the draft anchor;
  - an import of the provider.

**Scope.** Freezing makes these declarations immutable. A defect requires an
author-approved, versioned successor and invalidates dependent evidence. (E)
is `FROZEN_UNPROVED` until its provider proves it, it is sealed with
`by exact QED.Provider.OneLoop.vertexLimit_existsUnique`, and a fresh audit
passes. The definitions (A)–(C) depend on infrastructure definitions
(`QED.Minkowski.metric`, `dot`, `lower`, `QED.Dirac.gamma`, `slash`) whose
bodies were not displayed in packet 1. That gap is finding
[F-12](FINDINGS.md); it is to be closed by packet 1b. (Closed by D-12.)

## D-12. Packet 1b approved (author ruling)

**Ruling.** On 2026-11-08 the author approved packet 1b "as written". The
packet showed the exact committed text, docstrings included, of the five
infrastructure definitions in packet 1's closure. It also stated the evidence
for them:

- the Lean theorems `dot_eq`, `lower_eq`, `gamma_anticomm` (36.9), and
  `slash_mul_slash`;
- an entry-by-entry comparison of `gamma` with (36.7);
- the packet-1 reviewer's checks of `dot`, `slash`, and the gamma matrices.

No dedicated independent review of packet 1b was run. The author was told this
and approved without one.

**Frozen anchors** (bound by [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json)):

| Anchor | Export | Source |
| --- | --- | --- |
| `QED/Frozen/Algebra/Metric.lean` | `QED.Minkowski.metric` | (2.2)–(2.4), p. 30 |
| `QED/Frozen/Algebra/Dot.lean` | `QED.Minkowski.dot` | (2.2), p. 30 |
| `QED/Frozen/Algebra/Lower.lean` | `QED.Minkowski.lower` | index lowering with $g_{\mu\nu}$, p. 217 (before (34.22)) |
| `QED/Frozen/Algebra/Gamma.lean` | `QED.Dirac.gamma` | (36.7)–(36.8), p. 227 |
| `QED/Frozen/Algebra/Slash.lean` | `QED.Dirac.slash` | (37.24), p. 238 |

All five are definitions in state `SEALED`.

**Packaging.**

- Each definition moved out of `QED/Algebra/Minkowski.lean` or
  `QED/Algebra/Dirac.lean` into its own frozen file, with its export name
  unchanged. Those two modules now `public import` the frozen files and keep
  only the proved properties.
- A script confirmed that each frozen docstring and declaration is
  byte-identical to the text committed at `f0f51d5`, which is the text shown to
  the author.
- `pp.all` printing of each definition gave byte-identical output before and
  after the move. Its elaborated meaning is therefore unchanged.
- The bytes of packet 1's files (A)–(E) did not change, and neither did their
  ABI hashes.

**Closures.** Every definition closure in the manifest is now transitive over
frozen files:

- `dot` and `lower` close over `metric`;
- `slash` closes over `metric`, `lower`, and `gamma`;
- (A) closes over all five;
- (B) closes over `metric` and `dot`;
- (C) closes over all five together with (A) and (B);
- (E) closes over all five together with (A)–(D).

The guard was shown to reject three more violations. An edited `metric` body
is reported as drift in `metric`, `dot`, `lower`, `slash`, and (A). A
whitespace-only docstring change and a second declaration in a frozen file
are rejected too.

**Scope.** This closes [F-12](FINDINGS.md). Packet 1's meaning is now
protected down to Mathlib. The definitions are immutable; a change requires an
author-approved, versioned successor.

## D-13. Provider binder convention for sealing

**Decision.** A provider theorem for a frozen theorem anchor whose binders
precede the colon states the same proposition with the same binders in the
same order, with two changes:

- the data binders are implicit;
- the hypotheses are `:= by assumption` auto-parameters.

**Reason.** The frozen-anchor guard accepts a `SEALED` body only of the form
`by exact <export>` (or `by simpa using <export>`), with no arguments. Inside
the anchor's proof the binders are local hypotheses, so a provider with
explicit binders does not close the goal. With implicit data binders, Lean
infers the data from the goal and discharges each hypothesis by `assumption`.
`autoParam T _` is reducibly `T`, so the proposition is unchanged. The
independent audit of (E) confirmed this: after erasing `autoParam`, the
provider's type is `Expr.eqv` to the frozen type, and `isDefEq` holds at
reducible transparency.

**First use.** `QED.Provider.OneLoop.vertexLimit_existsUnique` seals packet 1's
theorem (E) (D-11), on 2026-11-08.

## D-14. Packet 2 approved (author ruling)

**Ruling.** On 2026-11-08 the author approved packet 2, `lorentzGen`
included. The approved text was the exact Lean shown to the author, in an
untracked scratch file with SHA-256
`7e1b18e093acd3207c61b96202745a46c792cf8bfae5e42981dfb40f68403fc5`. Before
approval, an independent refute-first reviewer checked it against (40.3),
(62.39)–(62.40), (63.16)–(63.22), and decisions D-5 and D-13. The review
found no blocker and no error, and judged (G) and (I) true. Its two weak
findings and its nits were applied to the text the author saw: (I) was made
self-contained, and the docstrings were corrected.

**Frozen anchors** (bound by [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json)):

| Anchor | Export | Kind and state |
| --- | --- | --- |
| `QED/Frozen/Algebra/LorentzGen.lean` | `QED.Dirac.lorentzGen` | definition, `SEALED`; moved from `QED/Algebra/Dirac.lean`, with `pp.all` output unchanged |
| (F) `QED/Frozen/OneLoop/VertexOneLoop.lean` | `QED.OneLoop.vertexOneLoop` | definition from theorem (E), `SEALED` |
| (F′) `QED/Frozen/OneLoop/VertexOneLoopSpec.lean` | `QED.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop` | theorem, `SEALED`, landed together with (F); audited |
| (G₀) `QED/Frozen/OneLoop/IsFormFactorPair.lean` | `QED.OneLoop.IsFormFactorPair` | definition (literal predicate (63.18)), `SEALED` |
| (G) `QED/Frozen/OneLoop/FormFactorExistsUnique.lean` | `QED.OneLoop.existsUnique_isFormFactorPair_vertexOneLoop` | theorem; frozen `DRAFT_SORRY`, then `SEALED` and audited the same day |
| (I) `QED/Frozen/OneLoop/PauliFormFactorLimit.lean` | `QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_limit` | theorem; frozen `DRAFT_SORRY`, then `SEALED` and audited the same day |

**Packaging, as announced.**

- One declaration per file, each with its own imports.
- (F′)'s proof moved to the provider
  `QED.Provider.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop`, under
  the binder convention of D-13.
- (G) and (I) have the bodies `by sorry` and quarantined providers.
- A script confirmed that every frozen docstring and declaration is
  byte-identical to the approved text.

**Sealing.** (G) and (I) were frozen as `DRAFT_SORRY` in `3ae8cd2`. They were
then sealed by their providers, which use the shared facts in
`QED/OneLoop/FormFactorPair.lean`. An independent refute-first audit found
no defect in (F′), (G), or (I). It confirmed:

- the frozen bytes against the approved text;
- `pp.all` statement equality with only the frozen definitions imported;
- provider types `Expr.eqv` to the frozen types after erasing `autoParam`;
- standard axioms only;
- no smuggled premise;
- the form factors against (63.17)–(63.20). Numerically, B at m_γ = 0 and
  Λ = ∞ equals (63.20) to 8 digits.

**Scope** (stated to the author with the packet):

- The packet concerns the (62.40) diagram under D-5's regulators. The link to
  the Wick expansion (D-8, O-1, O-2) is a later packet.
- That the counterterm only shifts A (O-8) is the source's interpretation,
  not a theorem here.
- F₂(0) is replaced by the joint limit.

## D-15. Packet 3 approved (author ruling)

**Ruling.** On 2026-11-08 the author approved packet 3. The approved text was
the exact Lean shown to the author, in an untracked scratch file with SHA-256
`9b5be9259ed1d44de2ca1b8460354a60d4958f5b4b880c9c1821622ebb600b7a`.

Before approval, an independent refute-first reviewer checked the packet
against (62.39), (63.1)–(63.3), (64.2), and decision D-5. It found no blocker
and no error, and it proved (K), (N), and (M) itself. Its docstring findings
and its suggested name for (N) were applied to the text the author saw. Its
numerics confirmed the necessity of the order of limits in (M): the slope of
F₁ at q² = 0 grows like ln(m/m_γ), so a joint limit would be false.

**Frozen anchors** (bound by [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json)):

| Anchor | Export | Kind |
| --- | --- | --- |
| (J) `QED/Frozen/OneLoop/VertexFunction.lean` | `QED.OneLoop.vertexFunction` | definition, literal (62.39) through order e³ |
| (K₀) `QED/Frozen/OneLoop/IsChargeNormalized.lean` | `QED.OneLoop.IsChargeNormalized` | definition, literal predicate (63.1)–(63.2) |
| (K) `QED/Frozen/OneLoop/ChargeConditionExistsUnique.lean` | `QED.OneLoop.existsUnique_isChargeNormalized` | theorem |
| (N) `QED/Frozen/OneLoop/CountertermShift.lean` | `QED.OneLoop.isFormFactorPair_vertexOneLoop_iff_vertexFunction` | theorem (obligation O-8) |
| (M) `QED/Frozen/OneLoop/ChargeNormalizationLimit.lean` | `QED.OneLoop.isFormFactorPair_vertexFunction_dirac_limit` | theorem (F₁(0) = 1, (64.2)) |

The theorems were frozen as `DRAFT_SORRY` in `eae88a8`, with providers that use
the shared facts in `QED/OneLoop/ChargeCondition.lean`. They were then sealed.
An independent refute-first audit found (K), (N), and (M) PROVED. It
confirmed:

- the frozen bytes;
- `pp.all` statement equality;
- provider types equal up to `autoParam`;
- standard axioms only;
- Z₁ = 1 − A(0) derived, not assumed;
- the non-vacuity of (M), by a Lean proof exhibiting an actual pair;
- the logarithmic slope numerically. A script confirmed that every
frozen docstring and declaration is byte-identical to the approved text.

**Consequence.** (N) proves O-8, so packet 2's scope limit "the counterterm
only shifts A is an interpretation" no longer applies.

## D-16. Packet 4a approved (author ruling)

**Ruling.** On 2026-11-08 the author approved packet 4a, the four spinor
definitions included. The approved text was the exact Lean shown to the
author, in two untracked scratch files with these SHA-256 hashes:

- the declarations:
  `7ffc893fb717c4d3adb315897961d72cbface6a3ec44b30f93c05d71f58a1ca6`;
- the closure definitions:
  `97597951f350595183c51a6a003ab38a0203c74c87a17eb0fd3a793f4d81250e`.

Before approval, an independent refute-first reviewer checked the packet. It
compared the field geometry against p. 383, (64.6)–(64.7), and (64.15)–(64.17),
and checked the closure definitions against (38.3) and (38.6)–(38.12). It
found no blocker and no error. Its rename (`IsResponseMagneticMoment`) and
its docstring findings were applied to the text the author saw.

**Frozen anchors** (bound by [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json)):

| Anchor | Export | Kind |
| --- | --- | --- |
| `QED/Frozen/Algebra/Beta.lean` | `QED.Dirac.beta` | definition (38.8); moved from `QED/Algebra/Dirac.lean` |
| `QED/Frozen/Algebra/Bar.lean` | `QED.Dirac.bar` | definition (38.7); moved from `QED/Algebra/Spinor.lean` |
| `QED/Frozen/Algebra/RestSpinor.lean` | `QED.Dirac.restSpinor` | definition (38.6); moved |
| `QED/Frozen/Algebra/Spinor.lean` | `QED.Dirac.spinor` | definition, closed form of (38.12); moved, with `𝟙` written out |
| (R₀) `QED/Frozen/OneLoop/IsResponseMagneticMoment.lean` | `QED.OneLoop.IsResponseMagneticMoment` | definition (response definition of D-9) |
| (R) `QED/Frozen/OneLoop/ResponseMagneticMomentExistsUnique.lean` | `QED.OneLoop.existsUnique_isResponseMagneticMoment` | theorem |
| (R′) `QED/Frozen/OneLoop/LandeFactorLimit.lean` | `QED.OneLoop.landeFactor_isResponseMagneticMoment_limit` | theorem (g → 2(1 + α/2π)) |

The `pp.all` output of each moved definition is unchanged. (R) and (R′)
were frozen as `DRAFT_SORRY` in `3c630c5`, with providers that use
`QED/OneLoop/MagneticResponse.lean`, and were then sealed. An independent
refute-first audit found both PROVED. It confirmed:

- the frozen bytes, and `pp.all` equality of the moved definitions;
- statement equality;
- standard axioms only;
- that μ = e(Z₁ + A(0) + B(0))/(2m) and Z₁ = 1 − A(0) are derived;
- the e = 0 case, and non-vacuity, by Lean witnesses;
- the Breit identities numerically.

**Scope** (stated to the author with the packet):

- g → 2(1 + α/2π) is proved for the *response* definition. The source's
  wave-packet definition, and its equivalence with this one (O-24), are
  packet 4b.
- The response is read from the amputated vertex with on-shell spinors.
- The order of limits is q → 0⁺ first, at fixed regulators, then
  m_γ → 0⁺ and Λ → ∞ jointly (D-5).

## D-17. Design of packet 4b (author ruling)

**Ruling.** On 2026-11-08 the author decided three design questions for the
source's wave-packet definition of the magnetic moment ((64.4)–(64.7);
ruling D-9):

1. **Order.** Packet 4b comes before L1.VERTEX (the Wick-expansion
   derivation of the vertex, D-8).
2. **The position integral.** The source's
   μ = ∫d³x x¹⟨e|J²(x)|e⟩ / ⟨e|e⟩ comes from the non-decaying vector
   potential A = (0, Bx, 0). The formal definition uses the undamped integral
   and requires its **absolute convergence**. The proof must therefore show
   that the packet's current density decays fast enough that
   ∫|x||⟨e|J²(x)|e⟩| < ∞. No damping of the field and no momentum-space
   shortcut is used. This needs smoothness of the vertex in the momenta near
   the packet's support, and Fourier decay estimates.
3. **Wave packets.** Real, rotationally invariant packets
   f(p⃗) = φ(|p⃗|²/λ²), with φ real, smooth, compactly supported, and not
   identically zero. "Sharply peaked" means λ → 0⁺. The expectation value is
   normalized by ⟨e|e⟩, so no normalization constant is needed. Real φ has no
   orbital part, as the source intends.

**Scope.** These are design rulings. The exact declarations of packet 4b go
through the usual review and approval.

## D-18. Packet 4b approved (author ruling)

**Ruling.** On 2026-11-08 the author approved packet 4b. The approved text
was the exact Lean shown to the author, in one untracked scratch file with
SHA-256 `ec2af13ba6062a3c8e308423fa1b600041f2f598dbf01f53456e14bbfdc51231`.

Before approval, an independent refute-first reviewer checked the packet
against (64.4)–(64.9), (3.11), (3.18), (41.5), D-9 and D-17. It found no
blocker and no error. Its numerical checks confirmed:

- the tree vertex gives g → 2 as λ → 0⁺, with an O(λ²) approach;
- the position integral, computed directly, agrees with the reduced formula
  to about 10⁻⁶;
- the phase, the (2π)³ factors, and the cancellation of the derivative terms
  on the packet profile.

Its two recommended fixes were applied to the text the author saw: the O-3
identification is stated in (W₁)'s docstring, and (W₅) carries an existence
conjunct, as (R′) does. Four smaller suggestions were also applied: the
names `packetNormSq` and `integrable_and_tendsto_sourceMagneticMoment`, and
the docstring citations of (3.11) and D-17.

**Frozen anchors** (bound by [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json)):

| Anchor | Export | Kind |
| --- | --- | --- |
| (W₀) `QED/Frozen/OneLoop/OneParticleMomentum.lean` | `QED.OneLoop.oneParticleMomentum` | definition, (ω, k⃗) with ω from (3.11) |
| (W₁) `QED/Frozen/OneLoop/PacketCurrentDensity.lean` | `QED.OneLoop.packetCurrentDensity` | definition, ⟨e\|J²(x)\|e⟩ from (64.4), (64.8)–(64.9) |
| (W₂) `QED/Frozen/OneLoop/PacketNormSq.lean` | `QED.OneLoop.packetNormSq` | definition, ⟨e\|e⟩ with (41.5) |
| (W₃) `QED/Frozen/OneLoop/SourceMagneticMoment.lean` | `QED.OneLoop.sourceMagneticMoment` | definition, the source definition (64.4)–(64.7) |
| (W₄) `QED/Frozen/OneLoop/SourceMagneticMomentLimit.lean` | `QED.OneLoop.integrable_and_tendsto_sourceMagneticMoment` | theorem (O-24), `DRAFT_SORRY` |
| (W₅) `QED/Frozen/OneLoop/SourceLandeFactorLimit.lean` | `QED.OneLoop.landeFactor_sourceMagneticMoment_limit` | theorem (g → 2(1 + α/2π)), `DRAFT_SORRY` |

Each file holds its declaration byte for byte as approved. The `pp.all`
output of all six equals that of the approved scratch file, up to the names
of compiler-generated auxiliary proofs. The lemmas `dot_oneParticleMomentum`
and `oneParticleMomentum_pos` are in the ordinary module
`QED/OneLoop/OneParticle.lean`, as the author was told. (W₁) passes their
proofs to the vertex function. Proofs are irrelevant, and the lemma
statements are fixed by the vertex function's binders.

**Points stated to the author with the packet:**

- The current matrix element is ū₊(k′)V^μ(k′,k)u₊(k), with unit electron
  residues and no photon-leg factor (O-3), as for the response definition.
  The reviewer found that any photon-leg factor c(q²) with c(0) = 1 leaves
  the source μ unchanged at every λ.
- (W₄) requires absolute convergence of ∫x¹⟨J²⟩, the integral that
  defines μ. The stronger ∫|x||⟨J²⟩| < ∞ displayed in D-17 also holds, but is
  not part of the statement.
- The profile condition is that φ is nonzero somewhere on [0, ∞), since only
  those values enter.
- The packet limit comes first, so λ₀ may depend on m_γ, Λ and Z₁.

**Sealed.** (W₄) and (W₅) were frozen as `DRAFT_SORRY` in `d1d4688` and then
sealed by their providers. The (W₄) proof writes the current density as the
two-momentum Fourier integral of the packet amplitude
F(k, k′) = w(k′) w(k) M(k′, k). It then uses these facts:

- F is smooth with compact support;
- the first position moment converges absolutely (decay like (1 + |x|)⁻⁴,
  with no damping of the field) and equals (2π)³ (i/2) ∫ (∂ₖ − ∂ₖ′)F on the
  diagonal (Fourier inversion at the origin);
- the derivatives of the weights cancel on the diagonal;
- the narrow-packet limit of the resulting weighted average;
- the Breit-frame response gives (∂ₖ − ∂ₖ′)M = −4imμ at rest.

(W₅) applies the sealed (W₄) to the sealed (R) and (R′).

An independent refute-first audit found both PROVED. It confirmed:

- the frozen bytes against the approved scratch file, and unchanged ABI
  hashes;
- that the provider binders match the frozen statements, with no excess
  hypotheses;
- that the proof consumes the intended steps, with no vacuous route;
- non-vacuity by Lean witnesses (a `ContDiffBump` profile, μ from (R));
- the sign and constant of the moment formula and D(0) = −4imμ,
  numerically;
- standard axioms only.

## D-19. Design of L1.VERTEX (author ruling)

**Ruling.** On 2026-11-08 the author decided four design questions for the
Wick derivation of the vertex (L1.VERTEX; ruling D-8, obligations O-1, O-2):

1. **Scope.** The object defined from the Wick contractions is the 1PI vertex,
   as in the source's (62.39): iV^μ is the sum of the 1PI contractions of the
   interaction terms through order e³. The theorem is that it equals the
   frozen Z₁eγ^μ + V^μ_1loop. The 1PI selection excludes vacuum, disconnected
   and leg-correction terms, so Furry's theorem and the normalization
   Z(0, 0, 0) = 1 are not needed.
2. **Counterterms.** The expansion uses the full counterterm Lagrangian
   (62.2)–(62.3) with free coefficients: the vertex counterterm δ₁ = Z₁ − 1
   and the two-point counterterms δ₂, δ_m, δ₃, each counted as order e². The
   theorem must hold for all values of δ₂, δ_m, δ₃, which shows that only δ₁
   reaches the 1PI vertex at order e³.
3. **Loop momenta.** Momentum is conserved at each vertex. For a one-loop
   graph the loop momentum flows on the lowest-labelled line of the unique
   cycle, and the value is integrated with packet 1's energy-first
   prescription (M1) at fixed ε > 0, then compared with the frozen vertex. A
   lemma proves that every connected contraction at this order has at most
   one loop, and that the routing choice does not matter.
4. **Generality.** Contractions, fermionic signs and the 1PI predicate are
   defined for any number of vertices of each kind, for reuse at two loops.
   The momentum-space values and the theorem cover only order ≤ e³.

**Scope.** These are design rulings. The exact declarations go through the
usual review and approval.

## D-20. Packet 5 approved (author ruling)

**Ruling.** On 2026-11-09 the author approved packet 5, the Wick derivation
of the vertex. The approved text was the exact Lean shown to the author, in
one untracked scratch file with SHA-256
`6933d7da4abc57dfb10cb4bf15cd5d2d8b80fa25e96e7a71be5eca4f7a71c206`.

Before approval, an independent refute-first reviewer checked the packet
against D-8, D-19 and the source's (58.17)–(58.21), rules 8–10, (62.2)–(62.3),
(62.12), (62.28) and (62.39)–(62.40). It found no blocker. Its checks:

- a literal Python transcription of all the definitions shows (W₁) holds,
  with nonzero δ₂, δ_m, δ₃. Only the bare and δ₁ trees and the 6 labelled
  vertex-correction contractions (all of sign +1) are 1PI, and each loop
  contraction equals the frozen integrand after a translation of ℓ;
- the fermionic sign agrees with an explicit Grassmann-algebra computation;
- (W₂) follows from (W₁) and the frozen characterization of the one-loop
  vertex (checked in Lean).

Its findings (out-of-domain docstrings, an equivalent form of `IsOnePI`,
names, style) were applied to the text the author saw.

**Frozen anchors.** All 26 declarations are in `QED/Frozen/Wick/`, one per
file, and bound by [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json):

- 24 definitions, sealed when frozen: `VertexKind`, its `Fintype` instance,
  `VertexKind.order`, `VertexKind.photonSlots`, `FermionVertex`, `PhotonSlot`,
  `Contraction`, `fermionSign`, `FermionLine`, `photonKey`, `PhotonLine`,
  `Line`, `Line.ends`, `Joined`, `IsOnePI`, `externalMomentum`, `IsLoopLine`,
  `lineMomentum`, `psiMomentum`, `photonMomentum`, `vertexFactor`,
  `contractionAmplitude`, `contractionValue`, `wickVertex`;
- (W₁) `QED.Wick.wickVertex_eq` (O-1, O-2) and (W₂)
  `QED.Wick.tendsto_wickVertex`, frozen as `DRAFT_SORRY` with quarantined
  placeholder providers.

Each file holds its declaration byte for byte as approved. Each file's
imports include the candidate's `Fintype` and `Perm` imports, so that
instance resolution matches. The `pp.all` output of all 26 equals that of the
approved scratch file, up to attribute markers and the names of
compiler-generated auxiliary proofs and matchers.

**Points stated to the author with the packet:**

- Values off the source domain are not meaningful, and the docstrings say
  so. That domain is the 1PI contractions at order ≤ e³ with ε > 0.
- The lemma promised in D-19.3 (at most one loop, and the routing choice does
  not matter) is internal to the proof of (W₁).
- The labelled photon-counterterm factor is half the Feynman rule (62.12).
- (W₁) has no hypotheses. It covers O-1 and O-2, not the residues of O-3.

**Sealed.** (W₁) and (W₂) were frozen as `DRAFT_SORRY` in `6d5c700` and then
sealed by their providers.

(W₁) combines two results:

- **The classification of the 1PI contractions** of every vertex sequence of
  order ≤ 3 (`QED/Wick/Classification*.lean`):
  - the empty, single-counterterm and two-vertex cases contribute nothing;
  - the two trees give i(1 + δ₁)eγ^μ;
  - for three gauge vertices the 1PI contractions are exactly the six
    vertex-correction chains, each of sign +1.
- **The evaluation of each chain** (`QED/Wick/ChainValue.lean`): the routing,
  the index contraction to γ^ρ S̃(p′+ℓ) γ^μ S̃(p+ℓ) γ^ν, and translation
  invariance of the energy-first integral, which needs no integrability.

(W₂) applies the sealed (W₁) and the frozen characterization (F′).

An independent refute-first audit found both PROVED. It confirmed:

- the frozen bytes and all 26 ABI hashes;
- that the provider statements equal the frozen ones up to the D-13
  convention;
- that the proofs consume the full classification, with non-vacuity shown by
  a Lean witness (`chainContraction 0 1 2`);
- a Python brute force with explicit Grassmann reordering;
- standard axioms only;
- that the guard change is sound.

**Guard change (orchestrator).** `scripts/check_frozen_anchors.py` required
every definition anchor to use a literal `def`. Packet 5 is the first to
freeze an `inductive`, `abbrev`s and an `instance`. Rather than rewrite the
approved text, the guard now accepts the definitional keywords `def`,
`abbrev`, `inductive`, `structure` and `instance`. It still rejects `axiom`,
`opaque`, `constant` and every other keyword. None of the accepted keywords
can carry an unproved claim.

## D-21. Design of L1.ASSEMBLY (author ruling)

**Ruling.** On 2026-11-09 the author decided three design questions for the
assembled one-loop result (L1.ASSEMBLY):

1. **Form.** One new headline theorem whose statement starts from the Wick
   vertex (packet 5). Near the regulator limit a charge-normalizing δ₁ exists.
   For each such δ₁:
   - the ε → 0⁺ limit of the Wick vertex is the vertex function;
   - F₂ is within η of α/2π;
   - both magnetic-moment definitions give g within η of 2(1 + α/2π).

   It is proved by combining sealed theorems, and its exact declaration goes
   through the usual review and approval.
2. **Residues (O-3): prove both sides.**
   - The electron side: derive the one-loop self-energy Σ from the Wick
     expansion, and prove that the on-shell conditions Σ(−m) = Σ′(−m) = 0
     ((62.27), (62.36)–(62.38)) fix δ₂ and δ_m and give unit electron
     residues.
   - The photon side: vacuum polarization with Π(0) = 0 (62.11). The fermion
     loop of Π is not regulated by the photon Pauli–Villars term of D-5, so
     this needs a fermion-loop regulator, to be put to the author as a
     separate regulator ruling before any declaration is drafted.

   The current matrix elements used by the magnetic-moment definitions (O-3
   in (W₁) of packet 4b and in (R₀)) are then tied to the model's full
   amplitude, not taken as a modeling identification.
3. **Evidence.**
   - A rebuild in a fresh clone at the recorded commit, with an axiom report
     for every sealed theorem and an independent end-to-end refute-first
     audit of the whole chain.
   - A Palomar-style Comparator challenge for the headline theorem.
   - `docs/ERRATA-AND-DEVIATIONS.md`, written from the findings ledger, with
     each erratum verified against the pinned PDF.

**Scope.** These are design rulings. The regulator for Π, and every exact
declaration, go through the usual review and approval.

## D-22. Fermion-loop regulator for the photon side of O-3 (author ruling)

**Ruling.** On 2026-11-09 the author chose the regulator for the vacuum
polarization Π (the photon side of O-3, D-21): **Pauli–Villars regulator
fermions as new fields of the Wick model.**

- **Masses and coefficients.** The regulator fermions have masses M₁, M₂ and
  coefficients c₁, c₂, with c₀ = 1 for the electron, Σcᵢ = 0 and
  Σcᵢ Mᵢ² = 0.
- **Effect.** Closed fermion loops become absolutely convergent and gauge
  invariant. They are integrated by M1 at fixed ε, like the rest of the model.
- **Versioning.** The extended model is a versioned successor of packet 5's
  vertex kinds. Packet 5's theorems carry over, because the 1PI vertex has no
  closed fermion loop at this order.

**Scope.** The exact successor declarations, the order of the regulator-mass
limit relative to the D-5 limits, and the statement of Π(0) = 0 go through
the usual review and approval.

## D-23. Design of O-3 (author ruling)

**Ruling.** On 2026-11-09 the author decided two design questions for the
residues (O-3; D-21, D-22):

1. **Full LSZ amplitude.**
   - Define the whole connected order-e³ three-point function from the Wick
     expansion, leg corrections included, and its LSZ on-shell amplitude as
     a limit with inverse propagators.
   - Prove that it equals ū(p′)V^μ(p′, p)u(p) ε_μ when the counterterms
     satisfy the on-shell conditions. These are (62.27) and (62.36)–(62.38)
     for the electron, with Σ derived from the Wick two-point function
     ⟨ΨΨ̄⟩, and (62.11) for the photon, with Π derived from ⟨AA⟩ and the
     regulator fermions of D-22.
   - Prove that the on-shell conditions fix δ₂, δ_m and δ₃ uniquely.

   The current matrix elements used by the magnetic-moment definitions are
   then the model's LSZ amplitude, not a modeling identification.
2. **General successor of the Wick model.** A versioned successor of packet 5
   allows arbitrary external field content (external Ψ, Ψ̄ and A fields) and
   includes the regulator-fermion fields. A theorem shows that packet 5's
   three-point objects are a special case, so its sealed results carry over.
   The machinery is reusable at two loops.

**Scope.** These are design rulings. The exact declarations, including the
form of the LSZ limit, the ordering of the regulator limits, and the
treatment of on-shell legs, go through the usual review and approval.

## D-24. Packet 6a approved (author ruling)

**Ruling.** On 2026-11-09 the author approved packet 6a, the general Wick
model. The approved text was the exact Lean shown to the author, in one
untracked scratch file with SHA-256
`540dc04cb5ba096ad22707023ffd190895529aa7b14eba636cd71f0086bde0ad`.

**How the regulator fermions enter.** The author explicitly approved this
reading of D-22. The regulator fermions are fields of the Wick model, but
they are carried as a flavoring of the gauge vertices: each gauge vertex is
`e Ψ̄_f A̸ Ψ_f` for some flavor f. The flavorings that a contraction preserves
are summed, with the closed-loop coefficients c_f, inside the loop
integrand. This is the same Wick sum, regrouped. It is needed because, for a
single flavor, the vacuum polarization is not integrable under M1, so
integrating flavor by flavor would give 0. Packet 5's vertex kinds, fields,
photon key and vertex factor are reused unchanged.

**Review.** An independent refute-first reviewer found one blocker in the
first draft: the flavors were integrated separately. The fix above resolved
it. The reviewer confirmed:

- (Y₁) is true;
- the fermionic sign agrees with an explicit Grassmann reordering in 4934
  cases;
- the routing is conserved and unique on every connected contraction with at
  most one loop in the relevant functions;
- the bound K ≤ 2nf + nA + 1 ensures at most one loop;
- the regrouping preserves every contraction count and symmetry factor;
- the regulated integrand decays like λ⁻⁶;
- the definitions reproduce Σ (62.28) and Π (62.12), as values as well as
  integrands.

**Frozen anchors.** All 33 declarations are in `QED/Frozen/WickModel/`, one
per file, bound by [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json):

- 32 definitions, sealed when frozen: `Params`, `Params.mass`,
  `Params.loopCoeff`, `Flavoring`, `fermionFlavor`, `Contraction`,
  `Preserves`, `fermionSign`, `ClosedLoop`, `loopWeight`, the line
  definitions, `IsBridge`, `ExternalsAttached`, `VerticesConnected`,
  `IsOnePI`, `externalMomentum`, `Line.label`, `IsLoopLine`, `lineMomentum`,
  `psiMomentum`, `photonMomentum`, `contractionAmplitude`,
  `regulatedAmplitude`, `contractionValue`, `onePIFunction`,
  `connectedFunction`;
- (Y₁) `QED.WickModel.wickVertex_eq_onePIFunction` (packet 5 is the special
  case), frozen as `DRAFT_SORRY` with a quarantined placeholder provider.

Each file holds its declaration byte for byte as approved, with the
candidate's Mathlib imports. The `pp.all` output of all 33 equals that of the
approved scratch file, up to attribute markers and auxiliary names.

**Points stated to the author:** the Pauli–Villars sign convention, the
source-facing domain of the values, and the intended evaluations of iΣ and
iΠ^{μν}.

**Sealed.** (Y₁) was frozen as `DRAFT_SORRY` in `f3bdc57` and then sealed by
its provider. The proof (`QED/WickModel/Compatibility*.lean`) transports packet
5's contractions to the general model along `Option ≃ Fin 1 ⊕ ·`, which
preserves:

- the sign;
- the lines with their ends and labels;
- the 1PI property;
- the loop line;
- the routing;
- the amplitudes.

Packet 5's classification then shows that the only flavoring a 1PI
contraction of order ≤ 3 preserves is the all-electron one, with weight 1.

An independent refute-first audit found (Y₁) PROVED. It confirmed:

- the frozen bytes and the ABI hash; the guard also failed on four deliberate
  mutations, as it should;
- statement equality;
- that the proof consumes the transport, the flavor collapse and the
  classification;
- non-vacuity, shown by a nonzero value proved in Lean;
- a brute-force check that the collapse genuinely depends on 1PI;
- standard axioms only.

## D-25. Covariant form of the on-shell conditions (author ruling)

**Ruling.** On 2026-11-09 the author chose the literal covariant form for the
on-shell conditions of packet 6b (O-3; D-21, D-23):

- **Decompositions.** Prove, as existence-and-uniqueness theorems on the ε → 0⁺
  limit:
  - Σ(p) = A(p²)p̸ + B(p²)m, Lorentz invariance included;
  - Π^{μν}(k) = Π(k²)(k²g^{μν} − k^μk^ν), the transversality (62.6)–(62.7),
    from the Pauli–Villars conditions.
- **Definitions.** Define Σ(p̸) = A(−p̸²)p̸ + B(−p̸²)m and Π(k²) from these.
- **Conditions.** State Σ(−m) = Σ′(−m) = 0 (62.27) and Π(0) = 0 (62.11)
  literally.

The covariance is needed anyway for the LSZ amplitude in moving frames.

**Consequence for the packet structure.** Each decomposition is an
existence-and-uniqueness theorem whose objects are then defined from it. So
packet 6b is staged:

- **6b-1:** the two frozen ∃! theorem goals (limit plus decomposition).
- **6b-2:** after they are proved, the definitions of A, B, Σ(p̸) and Π(k²); the
  on-shell predicates; and the theorems that the conditions fix δ₂, δ_m and
  δ₃ uniquely.

## D-26. Packet 6b-1 approved (author ruling)

**Ruling.** On 2026-11-09 the author approved packet 6b-1 as written. The
approved text was the untracked scratch file with SHA-256
`a321cbc104285d9c6983d881d9b381004d2ce1e285004477fca249901696a9c0`.

- **(Z₁)** `QED.WickModel.selfEnergy_existsUnique`. For m, m_γ, Λ > 0:
  - the one-loop self-energy integrands are integrable in both M1 stages for
    every ε > 0;
  - Σ_ε(p) = (1/i)[iΣ_ε(p)] tends, as ε → 0⁺, to A(p²)p̸ + B(p²)m for a unique
    pair of functions on p² > −(m + min(m_γ, Λ))². That region lies below both
    photon thresholds; it was narrowed from the first draft so that A and B
    stay real.
- **(Z₂)** `QED.WickModel.vacuumPolarization_existsUnique`. Under the
  Pauli–Villars conditions:
  - the regulated loop integrands are integrable for every ε > 0;
  - Π^{μν}_ε tends to the transverse form Π(k²)(k²g^{μν} − k^μk^ν) for a
    unique Π on k² > −4m².
- **Regulator masses.** The author explicitly ruled that the regulator
  fermions are heavier than the electron, M₁, M₂ > m. This keeps the electron
  pair threshold the lowest and Π real on the domain. It costs nothing later,
  since the regulator masses go to infinity anyway.

**Review.** An independent refute-first reviewer found both statements true,
with numerical evidence:

- the limit exists;
- the form A p̸ + B m holds exactly;
- A and B are frame-independent;
- Π is exactly transverse in the limit, though not at finite ε.

Its one blocker, that integrability was not asserted, so the Pauli–Villars
hypotheses did no work, was fixed by the integrability conjuncts.

**Frozen anchors.** `QED/Frozen/WickModel/SelfEnergyExistsUnique.lean` and
`VacuumPolarizationExistsUnique.lean`, both `DRAFT_SORRY`, with `pp.all`
statements equal to the approved file's. The (Z₁) provider already carries
the proof `QED.WickModel.selfEnergy_existsUnique_of_twoPoint`
(`QED/WickModel/SelfEnergyExistsUnique.lean`). The (Z₂) provider is a
placeholder.

**(Z₁) sealed.** (Z₁) was sealed by its provider after an independent
refute-first audit found it PROVED. The audit confirmed:

- the frozen bytes and the ABI hash, and statement equality up to the D-13
  convention, with no excess binders;
- integrability for every p and ε > 0;
- the limit A = A_loop − δ₂ and B = B_loop − δ_m, with the Feynman-parameter
  forms matching (62.33) with the Pauli–Villars logarithm, signs included;
- an independent numerical check that converges linearly in ε to a nonzero
  limit;
- non-vacuity, by Lean witnesses;
- standard axioms only.

**(Z₂) sealed.** (Z₂) was sealed by its provider after an independent
refute-first audit found it PROVED. The proof
(`QED/WickModel/VacuumPolarization*.lean`) gives the closed form
Π(s) = −δ₃ + (e²/2π²)∫x(1−x)Σ_f c_f log(M_f² + x(1−x)s). The non-transverse
terms cancel pointwise in x, and the covariance boundary term vanishes only
because of both Pauli–Villars conditions. The audit confirmed:

- the frozen bytes, with the guard rejecting five deliberate mutations, and
  the ABI hash;
- statement equality with no excess binders;
- that integrability fails if either Pauli–Villars condition is dropped;
- an independent computation of Π from the regulated integrand, which
  matches the closed form to 3×10⁻⁵ and is frame-independent;
- transversality only in the limit, as stated;
- (62.25) recovered as the regulator masses grow;
- non-vacuity, by Lean witnesses;
- standard axioms only.

## D-27. Packet 6b-2, electron half, approved (author ruling)

**Ruling.** On 2026-11-09 the author approved the electron half of packet
6b-2 as written. The approved text was the untracked scratch file with
SHA-256 `c128f91154d408e21dbf12c7bd7b856860917d5182f8e49aca5533f830712da6`.

- **(Z₃)** `selfEnergyAB`: the unique (A, B) of the sealed (Z₁).
- **(Z₃′)** `selfEnergyAB_spec`: its characterization.
- **(Z₄)** `selfEnergySlash`: Σ(z) = A(−z²)z + B(−z²)m, the source's Σ(p̸) with
  p² = −p̸².
- **(Z₅)** `IsElectronOnShell`: Σ(−m) = 0 and Σ′(−m) = 0. The derivative is
  taken through a clamp onto an interval around −m inside the domain, which
  does not change it.
- **(Z₆)** `electronCounterterms_existsUnique`: these conditions fix (δ₂, δ_m)
  uniquely.

**Review.** An independent refute-first review found no statement blockers.
The reviewer and a separate proof worker both proved (Z₃′) and (Z₆) with
standard axioms only. The unique pair, with a = A_loop and b = B_loop at
s = −m², is:

- δ₂ = a − 2m²a′ + 2m²b′;
- δ_m = b − 2m²a′ + 2m²b′.

δ₂ agrees with Peskin's Pauli–Villars δZ₂ up to O(1/Λ²). The renormalized Σ
agrees with Srednicki's (62.36) to 1e-11. A boosted-frame check confirmed
that the electron-leg factor needed by LSZ vanishes on shell with these
counterterms. The review's naming and docstring findings
(`selfEnergySlash`, a lighter domain proof) were applied to the text the
author saw.

**Frozen anchors.** All five are in `QED/Frozen/WickModel/`, and their
`pp.all` output equals the approved file's:

- (Z₃), (Z₄) and (Z₅) are definitions, sealed when frozen.
- (Z₃′) lands sealed in the same commit as (Z₃), by its provider (three lines
  from (Z₁)). A definition chosen from an existence-and-uniqueness theorem
  lands with its proved characterization.
- (Z₆) is `DRAFT_SORRY`. Its provider already carries the proof, from
  `QED/WickModel/ElectronOnShell.lean`.

**(Z₆) sealed.** (Z₆) was sealed by its provider after an independent
refute-first audit found (Z₃′) and (Z₆) PROVED. The audit confirmed:

- the frozen bytes, with the guard rejecting five deliberate mutations, and
  all five ABI hashes;
- statement equality with no excess binders;
- that the proof goes through (Z₃′), the explicit form A = A_loop − δ₂ and
  B = B_loop − δ_m, the explicit solution and the clamp lemma;
- a numerical check at 40 digits that Σ(−m) and Σ′(−m) vanish for the
  solution, including when Λ < m_γ;
- agreement with the Pauli–Villars analogue of (62.34)–(62.38), to O(1/Λ²);
- non-vacuity, Lean-checked at a concrete point;
- standard axioms only.

## D-28. Packet 6b-2, photon half, approved (author ruling)

**Ruling.** On 2026-11-09 the author approved the photon half of packet 6b-2
as written. The approved text was the untracked scratch file with SHA-256
`a999b172c97f234189babf3f84c57f1b2a83aefe5ebf3c2afc67b3e4b0e5ad1f`.

- **(Z₇)** `vacuumPolarization`: the unique Π of the sealed (Z₂).
- **(Z₇′)** `vacuumPolarization_spec`: its characterization.
- **(Z₈)** `IsPhotonOnShell`: Π(0) = 0 (62.11).
- **(Z₉)** `photonCounterterm_existsUnique`: this fixes δ₃ uniquely.

**Review.** An independent refute-first review found no blockers, and the
reviewer proved (Z₇′) and (Z₉) in scratch. It confirmed:

- the unique counterterm is δ₃ = Π_loop(0) = (e²/12π²)Σ_f c_f log M_f², the
  regulated analogue of (62.24);
- Π(0) is determined through lightlike k ≠ 0;
- non-vacuity, with explicit regulator values.

Its findings were applied to the text the author saw: by (62.10) the residue
is the projector P^{μν}, not 1; a term proof replaced `nlinarith`; and the
name is `vacuumPolarization`. It also noted points for 6c: the continuity of
Π at 0, taking ε → 0⁺ before q → 0, and that the photon leg touches only F₁.

**Frozen anchors.** All four are in `QED/Frozen/WickModel/`, and their
`pp.all` output equals the approved file's:

- (Z₇) and (Z₈) are definitions, sealed when frozen.
- (Z₇′) lands sealed with (Z₇), by a two-line provider from (Z₂).
- (Z₉) is `DRAFT_SORRY`. Its provider carries the proof, from
  `QED/WickModel/PhotonOnShell.lean`.

**(Z₉) sealed.** (Z₉) was sealed by its provider after an independent
refute-first audit found (Z₇′) and (Z₉) PROVED. The audit confirmed:

- the frozen bytes, with the guard rejecting three deliberate mutations, and
  all four ABI hashes;
- statement equality with no excess binders;
- that the proof goes through (Z₇′), the explicit form Π = −δ₃ + Π_loop and
  the explicit solution δ₃ = Π_loop(0);
- the closed form Π_loop(0) = (e²/12π²)Σ_f c_f log M_f², proved in Lean in
  scratch and checked numerically at 30 digits;
- agreement with (62.23)–(62.25), with the 1/ε pole replaced by the regulator
  sum, and an independent Wick-rotated four-dimensional computation of
  Π_loop that agrees to 5e-7;
- non-vacuity, Lean-checked at a concrete point where δ₃ = 0 is not on shell;
- standard axioms only.

One audit note is a wording correction: for (Z₈) the `pp.all` output equals
the approved file's up to the names of auto-generated auxiliary proofs.

## D-29. Packet 6c design: the LSZ amplitude (author ruling)

**Ruling.** On 2026-11-09 the author chose, for packet 6c (the full LSZ
amplitude of D-23):

- **Photon leg.** The photon is a background-field leg. Its line is amputated
  by the free photon propagator and the one-loop vacuum-polarization insertion
  is kept. At order e³ the amplitude is then ū′V^μu + eΠ(q²)ū′γ^μu. Since
  Π(0) = 0, the extra term vanishes as q → 0 and does not change the magnetic
  moment.
- **LSZ limit.** The limit is iterated. First ε → 0⁺ at off-shell external
  momenta. Then the electron momenta approach the mass shell along any path,
  and the limit exists and is the same for every path. The leg corrections
  vanish because Σ(−m) = Σ′(−m) = 0, and the external spinors sit at the limit
  momenta.
- **Connection.** The response and source magnetic moments are restated with
  the LSZ amplitude as the one-electron current matrix element. These are new
  definitions, successors of packets 4a and 4b. A theorem then shows that they
  give the same μ as the frozen ū′V^μu versions, so g → 2(1 + α/2π) holds for
  the model's own amplitude. This replaces the modeling identification O-3, as
  D-21 asked.

**Background.** A free electron cannot absorb an on-shell photon except at
q = 0, so in the magnetic-moment problem the photon is an external field, not
an asymptotic particle.

## D-30. Packet 6c-1 approved (author ruling)

**Ruling.** On 2026-11-09 the author approved packet 6c-1 as written. The
approved text was the untracked scratch file with SHA-256
`6b255afb74b2d4e8f79b77767f2e128bb83afde46ab9413a506ae92163a58d68`.

- **(L₁)** `lszAmplitude_existsUnique`: for m, m_γ, Λ > 0, regulator fermions
  as in (Z₂) and electron counterterms on shell (Z₅), two things hold.
  - Every one-loop connected contraction of the order-e³ function with one
    external fermion pair and one external photon has an integrable loop
    integrand, at every ε > 0 and all momenta.
  - The LSZ amplitude exists and is unique. It is the iterated limit of
    (1/i) ū_{s′}(p′) G^μ_ε(r′, r) u_s(p), where G is the connected function
    (X₂₉), amputated by the free external propagators. First ε → 0⁺ at
    off-shell r′, r, then (r′, r) → (p′, p) through off-shell momenta along
    every approach.

**Review.** An independent refute-first review found no blocker in the
statement. It confirmed:

- the binder classification, with no excess hypothesis. The electron on-shell
  conditions are not excess: with Σ(−m) = 0 alone the limit exists but has the
  wrong residue, (1 + 2Σ′(−m)) times the tree term. A photon on-shell condition
  would be excess, since the photon is a background field;
- the index, momentum and 1/i conventions;
- by enumeration, that the connected function contains exactly the tree and
  δ₁ terms, δ₂/δ_m and Σ on each electron leg, δ₃ and Π on the photon leg, the
  1PI loop, and tadpoles;
- that the tadpoles vanish exactly by oddness, and that the leg corrections
  tend to 0 on every approach (60-digit check, generic and tangent);
- non-vacuity and the uniqueness lemma, both in Lean.

Its one required fix was applied to the text the author saw: the Dirac-field
normalization is (41.25), not the Majorana (41.29). The photon-leg term at
fixed regulators is e·q²·[1/(q²+m_γ²) − 1/(q²+Λ²)]·Π(q²)·ū′γ^μu; it becomes
D-29's eΠ(q²)ū′γ^μu only in the regulator limit. Because m_γ > 0 it vanishes
as q → 0 for every δ₃, so the magnetic moment does not depend on δ₃.

**Frozen anchor.** (L₁) is in `QED/Frozen/WickModel/`, as `DRAFT_SORRY`, and
its `pp.all` output equals the approved file's. Its provider is a stub until
the proof lands. The definition `lszAmplitude` and its characterization,
the closed form and the restated magnetic moments follow in packet 6c-2,
after (L₁) is sealed.

**(L₁) sealed.** (L₁) was sealed by its provider after an independent
refute-first audit found it PROVED. The proof combines two helper theorems:

- every one-loop connected contraction is integrable at every ε > 0 and all
  momenta, by a case split over the classified contractions (1PI vertex loop,
  Σ on either electron leg, Π on the photon leg, tadpoles, whose decay comes
  from the Pauli–Villars conditions);
- the iterated limit exists, is unique, and equals
  ū′V^μu + e·q²·[1/(q²+m_γ²) − 1/(q²+Λ²)]·Π(q²)·ū′γ^μu. Its ingredients are
  the decomposition of the connected function into its 1PI part and the leg
  insertions, the off-shell vertex limit and its continuity up to the shell,
  the vanishing of the electron-leg insertions under Σ(−m) = Σ′(−m) = 0, and
  the continuity of the photon-leg insertion.

The audit confirmed:

- the frozen bytes, with the guard rejecting twelve deliberate mutations, and
  the ABI hash;
- statement equality with no excess binders;
- that the proof goes through the sealed (Y₁), (W₁), (Z₃′), (Z₇′) and (F′),
  and unpacks (Z₅) as the sealed (Z₆) provider does;
- the decomposition against an independent enumeration, and numerical checks
  of the photon-leg contraction and of the electron legs (double precision);
- non-vacuity, Lean-checked at concrete parameters with counterterms from
  (Z₆);
- a kernel replay of the new modules, and standard axioms only.

## D-31. Packet 6c-2 approved (author ruling)

**Ruling.** On 2026-11-09 the author approved packet 6c-2 as written. The
approved text was the untracked scratch file with SHA-256
`089503a751fe97934836d6ef7ed41f73188b58657cd7fe9cb0284d65206687fe`.

- **(L₂)** `lszAmplitude`: the LSZ amplitude M^μ_{s′s}(p′, p), the unique
  iterated limit of the sealed (L₁).
- **(L₂′)** `lszAmplitude_spec`: its characterization.
- **(L₃)** `lszAmplitude_eq`: M = ū′V^μu + e·q²·D(q²)·Π(q²)·ū′γ^μu, with
  D(q²) = 1/(q²+m_γ²) − 1/(q²+Λ²), for every δ₃.
- **(L₄)** `IsLSZChargeNormalized` and **(L₄′)** the theorem that it is
  packet 3's charge condition (K₀) at Z₁ = 1 + δ₁.
- **(L₅)** `IsLSZResponseMagneticMoment` and **(L₅′)** the theorem that it is
  packet 4a's (R₀) at Z₁ = 1 + δ₁.
- **(L₆)** `lszPacketCurrentDensity`, **(L₇)** `lszSourceMagneticMoment`, and
  **(L₇′)** the theorem that, as in (W₄), the position integral converges
  absolutely and the source moment tends to the response moment.

These restate the magnetic-moment definitions with the model's own LSZ
amplitude as the one-electron current matrix element, replacing the modeling
identification O-3 (D-21, D-29).

**Review.** An independent refute-first review found no blocker. It compared
(L₄), (L₅), (L₆) and (L₇) line by line with (K₀), (R₀), (W₁) and (W₃): the
only differences are the parameter binders and the LSZ amplitude in place of
ū′V^μu. No theorem has an excess hypothesis. It proved (L₂′), (L₃), (L₄′) and
(L₅′) in scratch, and sketched (L₇′), finding that the LSZ source moment equals
the packet-4b one at every packet width. Its docstring nits and two renames
were applied to the text the author saw. It also noted that, in the D-5 order
of limits, the photon-leg term vanishes at q → 0 through the factor q²D(q²),
not through Π(0) = 0, so (Z₈)/(Z₉) are not used in the g-factor chain; an
optional theorem for the headline packet could show that under Π(0) = 0 the
photon-leg term is O(q³) uniformly in m_γ and Λ.

**Frozen anchors.** All ten are in `QED/Frozen/WickModel/`. Their `pp.all`
output equals the approved file's up to the names of auto-generated auxiliary
proofs.

- (L₂), (L₄), (L₅), (L₆) and (L₇) are definitions, sealed when frozen.
- (L₂′) lands sealed with (L₂), by a two-line provider from (L₁).
- (L₃), (L₄′), (L₅′) and (L₇′) are `DRAFT_SORRY`. The provider of (L₃)
  already carries its proof, from `QED.WickModel.lszLimit_closedForm`; the
  others are stubs until their proofs land.
- The subtype proof in (L₃) names `QED.Minkowski.dot_sub_self_nonneg_of_onShell`
  from the non-frozen module `QED.Algebra.OnShell`; renaming that lemma would
  break the anchor.

**(L₃), (L₄′), (L₅′), (L₇′) sealed.** All four were sealed by their providers
after an independent refute-first audit found them, and (L₂′), PROVED. The
proofs:

- (L₃): the uniqueness in (L₁) applied to the closed form's limit property.
- (L₄′): at p′ = p the photon-leg term carries q² = 0; only the factor
  2p⁰ ≠ 0 is cancelled, so it holds for every e, including e = 0.
- (L₅′): in the Breit frame the photon-leg term is i·e·q³·D(q²)·Π(q²),
  bounded by C·q³.
- (L₇′): the LSZ source magnetic moment equals packet 4b's (W₃) at
  Z₁ = 1 + δ₁ for every packet width, because the photon-leg term's factor q²
  has vanishing gradient on the diagonal k′ = k; then the sealed (W₄) applies.

The audit confirmed:

- the frozen bytes, with the guard rejecting fifteen deliberate mutations, and
  all 115 ABI hashes;
- statement equality with no excess binders, and that no helper names or
  imports a draft anchor or its provider;
- the proof routes through the sealed predecessors, the photon-leg algebra
  and the moment argument, with numerical checks at double precision;
- non-vacuity in Lean at concrete parameters, and that (L₄) and (L₅) are not
  trivially true;
- standard axioms only.

Packet 6c is complete: the magnetic moments of packets 4a and 4b are now
restated with the model's own LSZ amplitude, and they agree with the original
ones.
