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
| D-32 | 2026-11-09 | Headline design, LSZ form: general Wick model with on-shell counterterms; no photon condition (holds for every δ₃); F₂ and both Landé factors in one statement; fixed regulator fermions | Author |
| D-33 | 2026-11-10 | Headline packet (the LSZ form factors and the headline theorem) approved as written and frozen; D-32 supersedes the first bullet of D-21 | Author |
| D-34 | 2026-11-15 | Phase 3 design: certified enclosures of the regulated one-loop Pauli form factor; integer interval arithmetic checked by the kernel; box-partition quadrature; CODATA 2022 α (±1σ) for the contribution bound | Author |
| D-35 | 2026-11-15 | Packet Q (Phase 3 theorem goals: three certified Pauli form-factor enclosures and the CODATA contribution bound) approved as written and frozen, without the optional corollary | Author |
| D-36 | 2026-11-16 | Phase 4 design: route A (4D Pauli–Villars, parametric subtraction); first milestone the full mass-independent A₁⁽⁴⁾; exact closed form; attribution unchanged | Author |
| D-37 | 2026-11-17 | Two-loop follow-ups: q² → 0 first (quantifier-form headline); Ward identity proved; single real counterterms, truncated; M_f → ∞ last; joint energy-first prescription; 1PI-vertex headline first | Author |

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

**Evidence completed (2026-11-15).** The headline was settled by D-32 and
D-33 and sealed after its audit. The evidence of item 3 is complete:

- **Fresh checkout.** A clone of `82c5dfd` from GitHub, built from the Mathlib
  cache, builds with no warnings. The guard passes (118 anchors, none
  draft), the module check passes, all 118 ABI hashes match, and an axiom
  report for the 28 theorem anchors and the five Comparator theorems shows
  only the standard axioms.
- **End-to-end audit.** An independent refute-first audit of the whole
  chain found the headline proved as advertised, with no FAIL or CONCERN.
  Its WEAK items are scope limits already documented as deviations: the
  model is its momentum-space Wick expansion, truncated at order e³, in
  Feynman gauge with fixed regulator fermions, and the independence of δ₃
  relies on taking q → 0 at fixed m_γ. Its own numerics reproduce
  F₂ → α/2π and the sign of g − 2.
- **Comparator challenge.** `lake comparator`, with con-ron, NanoDa and
  Lean's kernel registered as Palomar does, accepts the Solution at
  `fdfb568`. An editorial review of the Challenge found no blocker.
- **Errata record.** `docs/ERRATA-AND-DEVIATIONS.md` covers the LSZ amplitude
  and the headline: 7 errata, 15 deviations.

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

## D-32. Design of the headline theorem, LSZ form (author ruling)

**Ruling.** On 2026-11-09 the author decided four design questions for the
L1.ASSEMBLY headline (D-21), now that packet 6c gives the model's own LSZ
amplitude:

1. **Form.** The headline quantifies over the general Wick model's parameters
   with fixed e ≠ 0, m > 0 and regulator fermions. Near the regulator limit
   (m_γ → 0⁺, Λ → ∞), counterterms exist with the electron on shell (Z₅) and
   the LSZ charge condition (L₄); for every such choice the conclusions below
   hold. It is proved by combining sealed theorems.
2. **Photon condition.** Π(0) = 0 (Z₈) does not appear: the headline holds
   for every δ₃. At fixed regulators the photon-leg term carries the factor
   q²/(q² + m_γ²), so g does not depend on δ₃. The photon side (Z₈), (Z₉)
   stays proved but separate from the g chain.
3. **Contents.** One statement bundles F₂ within η of α/2π and both
   magnetic-moment definitions (response and wave-packet source, LSZ form)
   giving g within η of 2(1 + α/2π).
4. **Regulator fermions.** M₁, M₂ > m and the two Pauli–Villars conditions
   are hypotheses on fixed values; the limits are m_γ → 0⁺ and Λ → ∞ only.

**Scope.** These are design rulings. The exact declarations go through the
usual review and approval.

## D-33. Headline packet approved (author ruling)

**Ruling.** On 2026-11-10 the author approved the headline packet as written.
The approved text was the untracked scratch file with SHA-256
`6e716aaae2a5e1706c9be27eae4221209e3efb56483cf8d837447eb47abce526`.

- **(H₀)** `IsLSZFormFactorPair`: the decomposition (63.18) of the LSZ
  amplitude, on the spinor bases.
- **(H₀′)** `existsUnique_isLSZFormFactorPair`: for e ≠ 0 and q² > 0 the LSZ
  amplitude has exactly one form-factor pair.
- **(H)** `lszAmplitude_pauli_landeFactor_limit`: the headline theorem. For
  fixed model data with e ≠ 0, m > 0 and admissible regulator fermions, and
  a wave-packet profile, jointly as m_γ → 0⁺ and Λ → ∞: counterterms exist
  with the electron on shell, the LSZ charge condition and an LSZ response
  moment; and for every such choice the Pauli component of the LSZ
  form-factor pair is within η of α/2π for small q² > 0, and both LSZ
  magnetic-moment definitions give g within η of 2(1 + α/2π). It holds for
  every δ₃.

With the approval the author confirmed two points:

1. D-32 supersedes the first bullet of D-21 ("the ε → 0⁺ limit of the Wick
   vertex is the vertex function"). The meaning of the LSZ amplitude rests on
   the sealed (L₁)/(L₂′), and (L₃) ties it to the vertex function, which
   packet 5 ties to the Wick vertex.
2. As written, δ and R may depend on all of the model data and on the
   profile. The proof gives δ and R depending only on e, m and η; making that
   visible would need e and m split out of the model data, which D-32 does
   not require.

**Review.** An independent refute-first review found no blocker in the Lean
statements and no excess binders, and proved (H) as written from sealed
theorems in scratch. Its text findings were applied to the text the author
saw: the order of limits (q² → 0⁺ jointly with the regulator limit, as in
(I)), the role of δ₃ (arbitrary, not irrelevant), the claim about F₂ (backed
by the added (H₀′)), and the name.

**Frozen anchors.** All three are in `QED/Frozen/WickModel/`, and their
`pp.all` output equals the approved file's. (H₀) is a definition, sealed when
frozen. (H₀′) and (H) are `DRAFT_SORRY`; their providers carry the proofs,
from the helper modules `QED/WickModel/Headline{Spinor,Pair,}.lean`.

**(H₀′) and (H) sealed.** Both were sealed by their providers after an
independent refute-first audit found them PROVED. The audit confirmed:

- the frozen bytes, with the guard rejecting nineteen deliberate mutations,
  and the three ABI hashes;
- statement equality with no excess binders;
- that the proofs go through the sealed (K), (Z₆), (L₃), (L₄′), (L₅′), (R),
  (R′), (I), (N), (G) and (W₅), with the quantifier structure of (I), (R′)
  and (W₅);
- the spin sum Σ_s u_s ū_s = m − p̸ and the shift of the first form factor by
  the photon-leg coefficient, numerically at double precision;
- non-vacuity in Lean at concrete parameters (with δ₃ = 7): counterterms, an
  LSZ response moment with g > 2, and an LSZ pair with F₂ ≠ 0;
- standard axioms only.

## D-34. Design of Phase 3, certified numerics for the one-loop pilot (author ruling)

**Ruling.** On 2026-11-15 the author decided four design questions for Phase 3
of the outline (milestones NUM.ARITHMETIC, NUM.INTEGRATION, NUM.CERTIFICATE,
NUM.VALIDATION):

1. **Target.** Certify interval enclosures of the regulated one-loop Pauli
   form factor at a few fixed rational regulator points, with
   Λ = m²/m_γ and a small fixed q² > 0. On shell the Pauli coefficient of the
   Phase-2 vertex is (e²/8π²) times a two-dimensional integral of a rational
   function over [0,1]². Each enclosure becomes a theorem: every form-factor
   pair of the one-loop vertex has F₂/(e²/8π²) in a stated interval. The exact
   limit C₁ = 1/2 stays as proved in Phase 2.
2. **Arithmetic.** Integer (fixed-point or dyadic) interval arithmetic with
   outward rounding, with a soundness theorem relating each operation to the
   reals. Certificates are checked by Lean's kernel; `native_decide` stays
   forbidden. (Measured: integer computations of 10⁵ steps check in seconds;
   exact rationals exceed the kernel's recursion limit at a few hundred
   operations.)
3. **Quadrature.** An external script proposes an adaptive box partition of
   [0,1]²; the Lean checker bounds the integrand on each box by interval
   arithmetic and sums area × [min, max]. Its soundness theorem: if it
   accepts, the integral lies in the stated interval. Higher-order rules can be
   added later on the same arithmetic.
4. **α input.** The contribution bound a_e⁽¹⁾ = C₁ α/π = α/(2π) uses the
   CODATA 2022 value α⁻¹ = 137.035999177(21) with its standard uncertainty
   (±1σ), as a labeled, sourced external input; π comes from Mathlib's
   20-digit bounds.

**Scope.** These are design rulings. The exact declarations go through the
usual review and approval.

## D-35. Packet Q approved (author ruling)

**Ruling.** On 2026-11-15 the author approved packet Q, the Phase 3 theorem
goals, as written. The approved text was the untracked scratch file with
SHA-256 `411a2e71275e1241358e3679601c820c7b16d80cfd78c68fbe7b12a2764917b4`.

- **(Q₁), (Q₂), (Q₃)** `isFormFactorPair_vertexOneLoop_pauli_enclosure_ten`,
  `_hundred`, `_thousand`: at m_γ = m/10ᵏ, Λ = m²/m_γ (k = 1, 2, 3) and
  q² = m²/10⁴, the one-loop vertex has a form-factor pair, and every such
  pair has F₂ = (e²/8π²)·t with t in [0.7668, 0.7673], [0.9700, 0.9705] and
  [0.9966, 0.9971] respectively.
- **(Q₄)** `oneLoopAnomaly_mem_codata2022`: if α = e²/(4π) has α⁻¹ in the
  CODATA 2022 one-standard-uncertainty interval [137.035999156,
  137.035999198], then e²/(8π²) = α/(2π) lies in [0.0011614097319,
  0.0011614097323].

The author approved the packet without the optional corollary composing the
headline theorem (H) with (Q₄). The link from (Q₄) to the Phase-2 amplitude is
therefore by expression: e²/(8π²) is literally the limit of F₂ in (I) and of
g/2 − 1 in (H).

**Review.** An independent refute-first review recomputed the three
integrals by two methods agreeing to 20 digits (0.767046342640042,
0.970249461540062, 0.996867788949086). Each interval contains its value with
at least 2.3·10⁻⁴ to spare, and (Q₄)'s bound holds with margins of about
2·10⁻¹⁴. The review also:

- proved (Q₄) in scratch;
- reduced (Q₁), as drafted, to the integral bound at m = 1;
- confirmed that each statement holds for every m > 0.

Its findings were applied to the text the author saw:

- `e ≠ 0` was dropped from (Q₄), since it follows from the α interval;
- term proofs replace inline `by positivity`, so the statements create no
  auxiliary constants;
- a sentence claiming a particular proof route was removed;
- the CODATA value was pinned in `docs/SOURCES.md`;
- the names and labels were changed.

A prototype certificate at the hardest point closed with about 4,000 boxes in
12 seconds of kernel time.

**Frozen anchors.** All four are in `QED/Frozen/OneLoop/`, as `DRAFT_SORRY`
with stub providers, and their `pp.all` output equals the approved file's. The
certificate infrastructure (`QED/Numerics/`) lands with them: integer interval
arithmetic with soundness lemmas, the box-partition checker with its
soundness theorem `integral_bounds_of_check`, and validation tests that accept
correct certificates and reject invalid ones.

**(Q₁)–(Q₄) sealed.** All four were sealed by their providers after an
independent refute-first audit found them PROVED. How each is proved:

- (Q₄) follows from Mathlib's 20-digit bounds on π.
- (Q₁)–(Q₃) reduce, through the existence and uniqueness of the form-factor
  pair (G) and the Feynman-parameter representation of the Pauli coefficient,
  to the integral of the Pauli integrand at m = 1.
- That integral is written as ∫ 2(1 − y) = 1 minus a remainder whose interval
  extension is exact in x, and the remainder is enclosed by three certificates
  of 5105, 772 and 107 boxes. Lean's kernel checks them in about 10 seconds in
  total, without `native_decide`.

The data is generated by `scripts/numerics/gen_pauli_certificates.py`, whose
`--check` mode regenerates it and compares byte for byte. Its format,
semantics, checker revision and replay are in `certificates/README.md`.

The audit confirmed:

- the frozen bytes and the four ABI hashes, with the guard rejecting eleven
  deliberate mutations;
- statement equality with no excess binders;
- the soundness of every interval operation, including rounding direction,
  negative values and reciprocals near 0;
- that the checker tiles the half-open unit square exactly;
- the algebraic identity behind the extension and the reduction with the
  scaling in m;
- that the kernel rejects eight tampered certificates;
- an independent recomputation of the three integrals from the original
  integrand;
- standard axioms only.

Phase 3 for the one-loop pilot is complete.

## D-36. Design of Phase 4, two loops (author ruling)

**Ruling.** On 2026-11-16 the author decided, after a source and route survey:

1. **Route A.** Keep the four-dimensional regularization of the frozen model:
   Pauli–Villars photon (mass Λ), photon mass m_γ, Pauli–Villars regulator
   fermions and energy-first loop integrals. The Wick model is generalized to
   two loop momenta, the diagrams are given Feynman-parametric
   representations, and renormalization is subtractive, with the cancellations
   proved at fixed regulators before the limits Λ → ∞, m_γ → 0.
   Dimensional regularization (route B) was declined. It would need new
   foundations (meromorphic d-dimensional integrals, integration by parts,
   symbolic-d Dirac algebra) and a break from the frozen 4D model.
2. **First milestone.** The full mass-independent fourth-order coefficient
   A₁⁽⁴⁾ = 197/144 + π²/12 − (π²/2) ln 2 + (3/4)ζ(3), directly: the
   vacuum-polarization insertion together with the six diagrams without
   fermion loops. The mass-dependent terms (μ, τ) come later.
3. **End form.** An exact closed form, with the finite subtracted parametric
   integrals evaluated analytically. Certified higher-dimensional numerics is
   not the target.
4. **Attribution.** Rulings and approvals continue to be recorded under the
   author's name, Scott Armstrong.

**Sources.** The author will acquire the paywalled sources the route needs
(listed with verified DOIs in `docs/SOURCES.md` once pinned). Under D-2 their
bytes stay uncommitted in `sources/cache/`, with their SHA-256 hashes recorded.

**Consequences found by the survey** (to be settled in later rulings):

- The one-loop Ward identity Z₁ = Z₂ and the photon condition Π(0) = 0 become
  load-bearing at order e⁵. The "for every δ₃" of D-32 does not carry over.
- The regulator-fermion masses must be removed by a limit M_f → ∞.
- The counterterms need order-e⁴ parts.
- The frozen single-loop-momentum prescription needs a two-loop successor.

**Scope.** These are design rulings. Every exact declaration goes through the
usual review and approval.

## D-37. Two-loop design follow-ups (author ruling)

**Ruling.** On 2026-11-17, after the two-loop derivation
(`docs/TWO-LOOP-DERIVATION.md`) and its review, the author decided:

1. **Order of limits and headline form.** At order e⁵ the joint limit in q²
   and the photon mass does not exist. For q² ≠ 0 the order-e⁴ Pauli form
   factor carries an infrared logarithm ~ q² ln m_γ (BMR-I p. 834). So
   q² → 0⁺ is taken first at fixed regulators, uniformly over on-shell pairs,
   as in D-5. The headline uses the quantifier form: for every η there are δ
   and R such that, for regulators beyond the thresholds and admissible
   counterterms, there is a q₀ > 0 (depending on the regulators) with
   |16π⁴[e⁴]F₂ − A₁⁽⁴⁾| < η for all pairs with 0 < q² < q₀.
2. **Ward identity.** The one-loop identity δ₁ = δ₂ (Z₁ = Z₂), needed for the
   infrared cancellation, is proved as a theorem at fixed regulators from the
   frozen on-shell conditions, not imposed.
3. **Counterterms.** Each counterterm stays a single real number, and the
   expansion is truncated. Separating the orders is a proof obligation.
4. **Regulator fermions.** Their masses are removed last. First q² → 0⁺, then
   m_γ → 0 and Λ → ∞, then M₁, M₂ → ∞.
5. **Prescription.** The two-loop value is the joint energy-first integral:
   both loop energies first, then all six spatial components. "Nested equals
   joint" is a theorem for the insertion diagrams, where the frozen one-loop
   Σ and Π are reused.
6. **Amplitude.** The first two-loop headline is stated on the order-e⁵ 1PI
   vertex. An LSZ restatement can follow later.

**Scope.** These are design rulings. Every exact declaration goes through the
usual review and approval.

## D-38. Packet T1 approved (author ruling)

**Ruling.** On 2026-11-17 the author approved packet T1, the Wick model at
two loops, as written. The approved text was the untracked scratch file with
SHA-256 `187beadd22438d5395ee6744a6e0719fde0c71a888f3971b1cd2a2edf6ea8549`.
Packet 6a's parameters, contractions, flavorings, signs, lines, labels,
connectivity, `IsOnePI` and external momenta are reused unchanged.

Definitions, frozen in `QED/Frozen/TwoLoop/`:

- **(T₉), (T₉′)** `QED.TwoLoop.jointEnergyFirstIntegral` and
  `jointEnergyFirstIntegrable`: the joint energy-first integral of D-37.5 for
  `L` loop momenta (all energies first, then all spatial components) and the
  integrability of both its stages.
- **(T₁)–(T₃)** `IsChord`, `loopCount`, `chordMomentum`: a line is a chord
  when its ends are joined by lines of larger label (the complement of the
  spanning forest of maximal total label, O2-5's greedy rule); the number of
  loops is the number of chords; the chords, ordered by label, carry `ℓ 0`,
  `ℓ 1`, ….
- **(T₄)–(T₈)** `lineMomentum₂`, `psiMomentum₂`, `photonMomentum₂`,
  `contractionAmplitude₂`, `regulatedAmplitude₂`: the routing with several
  loop momenta (rule 8, CK-R (11)–(16)), and the amplitude as a function of
  the line momenta.
- **(T₁₀), (T₁₁)** `contractionValue₂`, `onePIFunction₂`: the value of a
  contraction with `loopCount C` loop momenta, and the 1PI function, the
  successor of (X₂₈).

Theorem goals, frozen as `DRAFT_SORRY` with stub providers in
`QED/Provider/TwoLoop/`:

- **(T₁₂)** `QED.TwoLoop.jointEnergyFirstIntegral_one`: at one loop the joint
  prescription is the frozen (D).
- **(T₁₃)** `QED.WickModel.contractionValue₂_eq_contractionValue`: a
  contraction with at most one loop has its packet 6a value.
- **(T₁₄)** `QED.WickModel.onePIFunction₂_eq_onePIFunction`: through order
  `K ≤ 2 nf + nA + 1` the new 1PI function is packet 6a's (O2-9).

**Design choices.** The author accepted all seven presented:

1. chords from the maximal-label spanning forest;
2. loop momenta indexed by `Fin L`;
3. the loop count computed, not capped;
4. an amplitude that takes the line momenta as an argument;
5. one joint integral for any number of loops;
6. one routing for every contraction, with the one-loop agreement a theorem;
7. the 1PI function only, with the connected function deferred to the LSZ
   restatement.

**Review.** An independent refute-first review, given the code and not the
writer's reasoning, found the definitions faithful to rule 8, CK-R and
D-36/D-37. It checked:

- the chord rule against O2-5's greedy rule;
- momentum conservation of the routing on 20,000 random contraction graphs;
- that all three theorem goals are true.

It proved (T₁₃) in scratch modulo one graph fact (with at most one loop the
chord is the loop line (X₂₁)). Its findings, all in docstrings, were applied
to the text the author saw.

**Frozen anchors.** Fifteen files, one declaration each, with `pp.all` output
equal to the approved file's.
The frozen-anchor guard (`scripts/check_frozen_anchors.py`) now accepts
Lean's subscript characters in declaration names, such as `lineMomentum₂`.
Eight negative controls on the staged tree were all rejected: a renamed
declaration, a changed manifest export, an import of a draft, a use of a
draft export, a use of a provider export, an unregistered `sorry`, a seal
without a manifest change, and a changed hypothesis.

**(T₁₂)–(T₁₄) sealed.** All three were sealed by their providers after an
independent refute-first audit found them PROVED. How each is proved:

- (T₁₂) follows from the measure-preserving equivalence `Fin 1 → X ≃ X`, in
  both stages, for every integrand (`QED/TwoLoop/JointIntegral.lean`).
- (T₁₃) splits on the loop count (`QED/TwoLoop/OneLoopEmbedding.lean`).
  - With at most one chord, the chords are exactly the loop lines (X₂₁)
    (`QED/TwoLoop/ChordLoopLine.lean`), so the routing (T₄) is the one-loop
    routing (X₂₂).
  - With no loop, the joint integral is evaluation at the empty family.
  - With one loop, the chord carries `ℓ 0` and (T₁₂) gives (D).
- (T₁₄) adds the bound that a 1PI contraction of order at most
  `2 nf + nA + 1` has at most one loop (`QED/TwoLoop/LoopBound.lean`). The
  lines that are not chords connect the vertices, so there are at least
  V − 1 of them, and field counting gives E ≤ V. (T₁₃) then applies term by
  term.

The audit confirmed:

- that the only change to each frozen file is its proof line, and the only
  change to the manifest is the three states, with the guard rejecting 15
  deliberate mutations;
- statement equality with no excess binders, checked by `Expr.eqv` after
  erasing the D-13 binder conventions;
- that the providers consume the intended lemmas and import no draft;
- the soundness of the graph arguments;
- non-vacuity: the one-loop vertex has `loopCount = 1`, is 1PI and appears
  in the sum of (T₁₄);
- standard axioms only.

Following its nit, the helpers of `LoopBound` were moved out of the frozen
namespace into `QED.TwoLoop.LoopBound`, so they cannot collide with a later
frozen name.

## D-39. Packet T2 frozen provisionally (author approval pending)

**Status.** Provisional. On 2026-11-17 the author put the campaign in
overnight mode: "Continue and do so in overnight mode now (defer all
approvals and proceed)", then "no you can freeze temporarily, pending
approval in the morning". Packet T2 was frozen under that instruction **without
the author having seen its text**. Its manifest entries record the approval
as provisional. If the author rejects or amends it, it gets a versioned
successor, and every result that depends on it is invalidated.

The frozen text is the untracked scratch file with SHA-256
`f99ab96d6708c2c186f10120ec4ad991f54a55130f84700c11aeb0a16caed577`:

- **(U₁)** `QED.TwoLoop.a1Four`: the target constant
  A₁⁽⁴⁾ = 197/144 + π²/12 − (π²/2) ln 2 + (3/4) ζ(3) (obligation O2-1),
  with ζ(3) written as the series ∑ₙ 1/(n+1)³.
- **(U₂)** `QED.TwoLoop.a1Four_bounds`, a theorem goal frozen as
  `DRAFT_SORRY`: −0.3285 < A₁⁽⁴⁾ < −0.3284. This is a numerical check of the
  transcription and does not feed the headline.

**Review.** An independent refute-first review recommended approval. It
checked the formula against Passera (2007) eq. (9) and BMR-I (1.7) (p. 830,
again on p. 853), reading the rendered page images. It confirmed:

- the normalization, as the coefficient of (α/π)² with α = e²/4π;
- that the series is summable;
- the parse of every term;
- the vacuum-polarization and no-fermion-loop parts;
- the enclosure.

It preferred the inlined series to Mathlib's complex `riemannZeta 3`. The
link between them is proved in `QED/Polylog/Basic.lean`. Its nits were
applied:

- a redundant import was dropped;
- citations for the two parts and the convention α/π = e²/4π² were added;
- the enclosure was widened from five significant digits to four decimal
  places. Any slip in a coefficient moves the value by at least 10⁻³, and
  the wider interval is far cheaper to prove.

**(U₂) sealed** (on its provisional text). The provider encloses ζ(3) by the
first 40 terms of the series plus telescoping tail bounds, and uses Mathlib's
six-digit bounds on π and nine-digit bounds on ln 2. The proved interval is
[−0.3284907, −0.3284778] (`QED/TwoLoop/A1FourNumerics.lean`). An independent
refute-first audit found it PROVED:

- only the proof line and the manifest state changed, and the guard rejected
  14 deliberate mutations;
- the provider and frozen statements are identical terms;
- the bounds and margins were recomputed exactly with rational arithmetic and
  with mpmath;
- standard axioms only.

The seal certifies the provisional text. If the author amends (U₂), it gets a
versioned successor.

## D-40. Packet T4 frozen provisionally (author approval pending)

**Status.** Provisional, under the overnight instruction recorded in D-39. It
was frozen **without the author having seen its text**, and its manifest
entry records the approval as provisional.

The frozen text is the untracked scratch file with SHA-256
`12ca5be0736828eaa211401f3eb0879b65ac00805001c2d9f83e4fe925a87d69`:

- **(WI₁)** `QED.WickModel.δ₁_eq_δ₂`, the one-loop Ward identity Z₁ = Z₂ at
  fixed regulators (Srednicki (68.13) and the on-shell paragraph after it,
  p. 405; O2-15; D-37.2). For `e ≠ 0` and `m, m_γ, Λ > 0`, if the electron is
  on shell (Z₅) and the charge condition (K₀) holds with `Z₁ = 1 + δ₁`, then
  `δ₁ = δ₂`. It is frozen as `DRAFT_SORRY`. Its provider is already written,
  from `QED/TwoLoop/WardIdentity.lean`, and awaits the seal audit.

**Review.** An independent refute-first review recommended approval. It
checked:

- the source, and the normalization δᵢ = Zᵢ − 1;
- that each hypothesis is necessary: Lean counterexamples without `he`,
  without (Z₅) and without (K₀) (only the e = 0 counterexample is kept in
  the repository, as `QED.TwoLoop.Ward.exists_counterexample_e_eq_zero`;
  the other two were in the reviewer's scratch files);
- the docstring claims;
- the choice of (K₀) over the LSZ form, which follows through (L₄′);
- that the helper proves exactly this statement, and that its mathematics is
  sound, with an independent quadrature giving zero to 10⁻³¹.

Its nits were applied:

- the citation of the on-shell paragraph on p. 405;
- the name `δ₁_eq_δ₂` instead of `delta₁_eq_delta₂`, matching the field
  names;
- the remark that `ε` and `δ₃` play no role.

The frozen-anchor guard now also accepts Lean identifiers that begin with a
Greek letter (other than λ, Π, Σ), such as `δ₁_eq_δ₂`. Seven negative
controls with Greek names were all rejected: a renamed declaration, a
changed export, a use of the draft, a use of its provider, a `sorry`, a seal
without a manifest change, and a changed hypothesis.

**(WI₁) sealed** (on its provisional text), by its provider from the parametric
Ward identity. An independent refute-first audit found it PROVED:

- only the proof line and the manifest state changed, with about 25
  deliberate mutations rejected, including some on Greek-letter names;
- after erasing the D-13 conventions, the provider and frozen types are
  `Expr.eqv`;
- the ABI hash was recomputed;
- no draft is in the provider's import closure;
- standard axioms only.

The audit also found a guard weakness that predates this packet: the guard
did not check where a declaration name ends, so a name followed by further
identifier characters (`δ₁_eq_δ₂ϊ`, `δ₁_eq_δ₂!`) was read as the shorter
name. The guard now checks that boundary and covers all of Lean's letter-like
ranges. Six mutations of this kind are rejected.

## D-41. Packet T3, the two-loop headline, frozen provisionally (author approval pending)

**Status.** Provisional, under the overnight instruction recorded in D-39. It
was frozen **without the author having seen its text**. The approval
request includes the two questions below.

The frozen text is the untracked scratch file with SHA-256
`9b346ad73fb2ad6843d2e4df1937d0f6a44501e0c68fd74632afdd526f14e688`. It
consists of:

- **(HV₁)** `QED.TwoLoop.vertexOrderFive`: the order-e⁵ 1PI vertex at fixed
  ε, `(1/i)` times `onePIFunction₂ P 1 1 5 − onePIFunction₂ P 1 1 4` at
  `(p', p, p' − p)`. The row index is outgoing and the column index
  incoming, as in (Y₁) and (W₂).
- **(HV₂)** `QED.TwoLoop.IsVertexOrderFiveLimit`: its ε → 0⁺ limit,
  entrywise.
- **(HV₃)** `QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit`, the
  headline theorem goal, frozen as `DRAFT_SORRY`. Fix `e ≠ 0` and `m > 0`.
  For every `η > 0` there is `R_M` such that, for all regulator fermions
  heavier than `m` and `R_M` that satisfy the Pauli–Villars conditions,
  there are `δ > 0` and `R` such that, for `0 < m_γ < δ` and `Λ > R`:
  - counterterms satisfying (Z₅), (K₀) and (Z₈) exist;
  - for every such choice there is `q₀ > 0` such that, at every on-shell
    pair with `0 < q² < q₀`, the order-e⁵ vertex has an ε → 0⁺ limit,
    every such limit has a form-factor pair (G₀), and every such pair has
    `‖16π⁴ F₂/e⁴ − A₁⁽⁴⁾‖ < η`.

**Questions for the author** (left open by D-37 and section 5.6):

1. **Threshold order.** The headline chooses `R_M` first and lets `δ, R`
   depend on `M₁, M₂`, reading D-37.1 with D-37.4 (masses removed last).
   The alternative, `δ, R` independent of `M_f`, would be a joint limit in
   all regulators, which needs uniformity in `M_f` that the plan does not
   prove.
2. **Joint `(m_γ, Λ)` limit.** The headline takes `m_γ → 0` and `Λ → ∞`
   jointly, which is the stronger form. Its truth rests on the S + C unit
   carrying no `(m²/Λ²) ln m_γ` remainder. That is supported numerically
   (section 11.3) and plausible by the Ward identity, but not yet proved.
   The alternative, `Λ → ∞` before `m_γ → 0`
   (`∃ δ, ∀ m_γ < δ, ∃ R, ∀ Λ > R`), is weaker and safer.

**Review.** Two independent refute-first reviews were run. The first, on the
drafter's version, required text changes only. It confirmed that:

- (HV₁) is exactly the order-5 part and misses no contraction;
- the normalization is right;
- `he` is necessary, since at e = 0 the conclusion is false;
- the binders are classified correctly;
- admissible counterterms exist.

It also asked for the two questions above to go to the author. The second
reviewed the revision. Its changes were:

- the labels (HV₁)–(HV₃);
- citing O2-27 as proved, items 1–2, for `e ≠ 0`
  (`QED/TwoLoop/CountertermScaling.lean`);
- the name, parallel to (I);
- a clause asserting that admissible counterterms exist, as in (H).

That review proved the existence clause true for every admissible regulator
choice, and showed the revised headline logically equivalent to the
drafter's version. Its nits, citing O2-27 items 1–2 and rewrapping lines
over 100 characters, were applied.

**Truth risks outside the text.** These obligations are not yet proved; if
one fails, (HV₃) is false as frozen and needs a versioned successor:

- O2-7: integrability, since a non-integrable contraction silently
  contributes 0;
- O2-20, O2-21: covariance and the cancellation of the q^μ term;
- O2-22: uniformity over the pairs;
- O2-19: decoupling of the regulator fermions;
- the joint-limit question above.

## D-42. Corrections to the overnight prose (2026-11-18)

**Status.** Record of corrections; no ruling.

An independent audit compared the prose written overnight on 2026-11-17
(commit messages, the progress ledger, `docs/TWO-LOOP-DERIVATION.md`,
`docs/TWO-LOOP-ENUMERATION.md`, STATUS and the README) with the Lean
statements. It found no wrong mathematics, and no claim that an unproved
result was proved. It did find wording that overstated a result or left out
hypotheses. The documents are corrected in place. Pushed commits are not
rewritten, so this entry is the correction of record for their messages:

- **cda92e2** said it proved "the exact vacuum-polarization unit value".
  What it proves is the evaluation of an explicit double integral,
  `QED.TwoLoop.VPUnit.integral_vpUnit` (= 119/36 − π²/3), and the spectral
  identity `integral_mul_log_eq_spectral`, which needs M ≠ 0 as well as
  k² > −4M². Both are helper-level facts about explicit integrals. That the
  double integral is the limit of the model's VP unit remains O2-8, O2-10
  and O2-13.
- **3934bc6** said momentum conservation "is necessary". It is argued to be
  needed (without it the routing is not conserved), not shown necessary in
  Lean. `QED.TwoLoop.Relabel.contractionValue₂_relabel` also assumes
  connected vertices (X₁₇) and external momenta summing to zero. The 1PI
  form, `contractionValue₂_relabel_of_isOnePI`, assumes momentum
  conservation, with connectedness supplied by the 1PI property.
- **2b65b47** said the parametric representation holds "without the U
  hypotheses". The hypotheses are replaced, not removed. The full
  representation `jointEnergyFirstIntegral_prod_inv_lineDenom_of_noSubdivergence`
  needs the no-subdivergence criterion; the energy step
  `integral_prod_lineDenom_eq_of_span` needs the spanning condition. The class
  statements use the loop matrices `class5LoopMatrix`. These are integer
  routings written for that file, not `lineMomentum₂`, and are matched to the
  class representatives numerically only. The doubled-line forms for S± and VP
  are assumed shapes of the Pauli–Villars-combined integrands, not derived from
  the model. Necessity of the criterion is not proved; the only evidence for it
  is a Monte Carlo check (`scripts/numerics/two_loop_crosschecks.py criterion`).
- **73dc087** stated the exact loop formula for "connected contractions with
  N ≥ 1". `QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq` also needs
  attached externals (X₁₆).
- **1872b4b** said "sequences of even order [have] none at all" among the
  kernel-checked facts. That statement comes from the Python enumeration
  (`scripts/numerics/two_loop_enumeration.py`) and is not kernel-checked. The
  Lean proof does not need it.
- **6c3b90f** stated the decoupling bound without its hypothesis.
  `QED.TwoLoop.VPUnit.abs_vpLimSum_sub_le` holds for M₁, M₂ ≥ m (= 1 in that
  module). It bounds the (m_γ, Λ)-limited explicit value, at helper level, not
  the model's VP unit.
- **277a494** listed "the Landen identities for Li2 and Li3" without a domain.
  `QED.Polylog.Li₂_one_sub_inv_add_Li₂_one_sub` and
  `Li₃_add_Li₃_one_sub_add_Li₃_one_sub_inv` are proved on [1/2, 1].

The same corrections, and two more, are applied to the ledger entry of
2026-11-18 and to the documents:

- the scalar parametric representation (e9ebf16) also needs spanning loop
  coefficients;
- the O2-15 proof used the ε = 0 parametric closed forms; the
  differential-identity route was the original plan.

Replay scripts for the numerical cross-checks run with these commits, which
had none in the repository, are added as
`scripts/numerics/two_loop_crosschecks.py`.

## D-43. Packets T2, T3 and T4 approved (author ruling)

**Ruling.** On 2026-11-18 the author approved all the provisionally frozen
packets: "Approved all provisionally approved packets". This covers:

- **D-39, packet T2:** the target constant (U₁) `QED.TwoLoop.a1Four` and its
  enclosure (U₂) `QED.TwoLoop.a1Four_bounds`.
- **D-40, packet T4:** the one-loop Ward identity (WI₁) `QED.WickModel.δ₁_eq_δ₂`.
- **D-41, packet T3:** the order-e⁵ vertex (HV₁), its ε → 0⁺ limit predicate
  (HV₂), and the two-loop headline (HV₃)
  `QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit`.

The approval is of the frozen texts as written. For (HV₃) it therefore
settles the two questions recorded in D-41, in the drafted reading:

1. **Threshold order.** The regulator-fermion threshold `R_M` comes first,
   and the photon-mass and Pauli–Villars thresholds `δ, R` may depend on
   `M₁, M₂`.
2. **Photon regulators.** `m_γ → 0` and `Λ → ∞` are taken jointly.

The manifest entries of the six declarations now record the approval
(`approval_version` 1). Their frozen bytes, ABI hashes and states are
unchanged: (U₂) and (WI₁) remain SEALED, and (HV₃) remains DRAFT_SORRY. The
seals of (U₂) and (WI₁), made on the provisional text, now stand on approved
text.

## D-44. Rulings on an independent strategy review (author ruling)

**Context.** On 2026-11-18 an independent reviewer (Gemini 4 Carbon, high
effort, read-only) critiqued the campaign's strategy. The orchestrator checked
its claims against the repository and put four questions to the author. The
author ruled on 2026-11-18:

1. **Scope of (HV₃) disclosed, LSZ lift deferred.** (HV₃) concerns the 1PI
   vertex at order e⁵ with one-loop counterterms (D-37). F₂ needs nothing more,
   but F₁ at order e⁵ is not renormalized there, and a two-loop LSZ or
   Landé-factor theorem would need counterterms graded by order. The scope is
   stated in the README; the lift is future work. ("ok")
2. **An integrability companion for the two-loop challenge.** A frozen
   statement that every class of `vertexOrderFive` is jointly energy-first
   integrable (T₉′) is to be drafted for the two-loop Comparator challenge,
   once the individual integrability of the Furry classes F₊, F₋ is proved
   (in progress). Its exact Lean text goes to the author for approval. ("yes")
3. **No provisional manifest state.** The manifest schema stays as it is. The
   author confirmed that the overnight freezes carried their provisional
   approval and approved all of them ("i gave provisional approval and i hereby
   approve all"). No provisional entry is outstanding: D-43 already recorded
   the approval of packets T2, T3 and T4.
4. **AGENTS.md.** Its stale bootstrap paragraph ("documentation and HQ
   maintenance tooling …") is replaced by a description of the current
   repository. ("fix it")

The review's other findings (STATUS.md staleness, the `.scratch` deletion in
`scripts/frozen_abi.py`) were fixed in a57d2db. Its engineering suggestions
for the corner limit went to that worker; its cleanup suggestions are deferred
until after the headline.

## D-45. HV0: every term of the order-e5 vertex is a genuine integral (author approved)

**Ruling.** On 2026-11-18 the author approved ("approve") the exact Lean
declaration (HV₀) `QED.TwoLoop.jointEnergyFirstIntegrable_vertexOrderFive`,
drafted under D-44 item 2. It is frozen at
`QED/Frozen/TwoLoop/JointEnergyFirstIntegrableVertexOrderFive.lean` with state
`DRAFT_SORRY` and provider
`QED.Provider.TwoLoop.jointEnergyFirstIntegrable_vertexOrderFive`.

**Statement.** Let `ε > 0` and let the regulator fermions satisfy the
Pauli–Villars conditions `1 + c₁ + c₂ = 0` and `m² + c₁M₁² + c₂M₂² = 0`. For
every 1PI contraction `C` with one external fermion pair and one external
photon whose vertices have total order exactly 5 (the terms summed in (HV₁)),
at all external momenta with momentum conservation and all external indices,
the integrand of its value (T₁₀) satisfies (T₉′). No mass, cutoff or on-shell
condition is assumed: at `ε > 0` every propagator is bounded.

**Review.** An independent refute-first audit returned APPROVE WITH NITS:
- coverage is exact: (HV₁) is the 1PI order-5 part, since every vertex has
  order at least 1;
- the integrand is that of `contractionValue₂`, checked by `rfl`;
- the hypotheses are satisfiable, with an explicit `Params`;
- no counterexample was found. The admitted contractions are the nine
  two-loop classes and the one-loop counterterm graphs; power counting is
  negative in every case.

Its nits concerned packaging, which the freezer supplies, a wider-than-needed
import, kept because it documents the link to (HV₁), and docstring wording,
left as approved.

**Proof status.** The two-loop classes are proved integrable:
`QED/TwoLoop/ClassIntegrable*.lean`, including the Furry classes (c0a709f).
The transfer from class representatives to arbitrary contractions, and the
one-loop counterterm graphs, are in progress. (HV₀) is a companion of (HV₃)
for the two-loop Comparator challenge; (HV₃) does not depend on it.

**Sealed (2026-11-18).** The body is `by exact
QED.Provider.TwoLoop.jointEnergyFirstIntegrable_vertexOrderFive`, from
`QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_order_five`
(`QED/TwoLoop/IntegrableOrderFive*.lean`). The proof splits by the number of
vertices: N ≤ 5 since every vertex has order at least 1. The 1PI lists for
N = 2 and part of N = 3 are computed empty. The remaining N = 3 and N = 4
contractions are relabellings of the δ₁, δ₂/δ_m and δ₃ counterterm
representatives, integrable at ε > 0. The N = 5 contractions are
relabellings of the nine class representatives. (T₉′) transfers along
relabellings by unimodular changes of loop momenta.

An independent refute-first seal audit returned PROVED:
- the frozen bytes changed only in the proof-body line, with prefix and suffix
  hashes matching;
- the manifest changed only `state`;
- the frozen and proof types are identical, and the ABI hash is unchanged;
- the axioms are propext, Classical.choice and Quot.sound;
- no smuggled hypothesis was found; the emptiness and relabelling claims are
  proved, not assumed;
- the guard and the build are clean.

## D-46. The two-loop headline (HV₃) sealed

**Status.** Record of a seal; no ruling.

On 2026-11-18 the frozen two-loop headline (HV₃)
`QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit`
(`QED/Frozen/TwoLoop/VertexOrderFivePauliLimit.lean`; frozen D-41, approved
D-43) was sealed. The body is
`by exact QED.Provider.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit`,
and the manifest state is SEALED. The frozen bytes outside the proof-body
line, the prefix and suffix hashes and the ABI hash are those approved in
D-43.

**Proof.** The provider applies the headline assembly
`QED.TwoLoop.HeadlineAssembly.pauliLimit_of_unitLimits` to two proved unit
links:
- X: `QED.TwoLoop.UnitXXi.xUnitLimit`;
- S + C: `SCUnitLimit.of_one`, from `scUnitLimitOne_of_corner` with
  `cornerMainLimit` and `cornerErrLimit`.

The assembly itself proves the VP and L links, the Furry cancellation, the
Ward identity (WI₁), the counterterm scaling and the sum of the five units.
Each unit enters with multiplicity +1, and the values add to A₁⁽⁴⁾:

| Unit | Value |
| --- | --- |
| L | 11/48 + ζ(2)/3 |
| VP | 119/36 − 2ζ(2) |
| S + C | −7/3 + 2ζ(2) ln 2 − ζ(3)/2 |
| X | 1/6 − 5ζ(2) ln 2 + 13/6 ζ(2) + 5/4 ζ(3) |
| **Sum** | 197/144 + π²/12 − (π²/2) ln 2 + (3/4) ζ(3) |

**Audit.** An independent refute-first seal audit returned PROVED with no
defects:
- the bytes, hashes and ABI hash match the approved text;
- the provider type equals the frozen type up to the D-13 auto-params;
- the assembly's conclusion is the frozen proposition;
- the transitive closure (72,556 constants, 436 modules) contains only
  propext, Classical.choice and Quot.sound;
- QED has no `sorryAx`, opaque, extern, `implemented_by` or `set_option`;
- every `Prop`-valued hypothesis on the route (`XUnitLimit`,
  `CornerMainLimit`, `CornerErrLimit`, `SCtHalfFormula`, `CrossedDom`, …) is
  discharged by a proved theorem;
- the unit values sum to `a1Four` within 7×10⁻³¹;
- the provider proves exactly the approved order of limits (D-43.1, D-43.2);
- the guard and the build are clean.

The truth risks recorded in D-41 (O2-7, O2-19 to O2-22, and the joint limit)
are thereby settled. The thresholds of L, S + C and X turn out to be uniform
in the regulator-fermion masses; only those of VP depend on them.

**Scope.** As stated in the README and in D-44 item 1, (HV₃) concerns the 1PI
vertex at order e⁵ with one-loop on-shell counterterms. The lift to a
two-loop LSZ or Landé-factor theorem is future work.

**Remaining for L2.ASSEMBLY:**
- the two-loop Comparator challenge, with (HV₃), (HV₀) and (U₂);
- a fresh-checkout rebuild.

## D-47. Comparator runs: the two-loop challenge, and the one-loop challenge repaired

**Status.** Record; the author approved running the Comparator on
2026-11-18 ("yes run the comparator").

**Two-loop challenge** (`QEDChallengeTwoLoop.lean`, `QEDSolutionTwoLoop.lean`,
`challenges/two-loop/comparator.json`; commit c5c8473). The Challenge imports
only Mathlib (941 lines). Its theorems:
- (HV₃);
- (HV₀);
- (U₂);
- a non-vacuity corollary `exists_pauliVillars_regulators`: admissible
  regulator masses and coefficients exist above every threshold;
- the three existence theorems (Z₁), (Z₂), (E), whose choices define
  compared values.

The Solution repeats the Challenge's declarations verbatim and proves each
theorem from the library.

**One-loop challenge drift.** A library module added since the one-loop seal
imports `Mathlib.Analysis.CStarAlgebra.Classes`, which changes the instance
path Lean selects for ℂ in every module importing `QED`. The one-loop
Challenge then no longer matched its Solution. Adding that import to
`QEDChallenge.lean` repairs it; the statements are unchanged. Re-run both
comparators whenever the library's import closure changes.

**Runs.** Both used `lake comparator` with a Palomar-style config: external
kernels con-ron and NanoDa, plus Lean's kernel. Each ran at commit c5c8473 on
a clean tree, niced and pinned to three cores.

| Challenge | Challenge sha256 | Solution sha256 | con-ron | NanoDa, Lean kernel | Time | Peak RSS |
| --- | --- | --- | --- | --- | --- | --- |
| Two-loop | b4a3a273…7cfabf | 28dc580a…23b012 | accepted 71,746 declarations | accept | 20 min 28 s | 3.7 GB |
| One-loop | 44352749…037924 | 34a8c4d6…a8724b75d | accepted 56,067 declarations | accept | 2 min 20 s | 0.9 GB |

Both runs end with "Your solution is okay!".

**Guard.** `scripts/check_frozen_anchors.py` now also recognises the
Challenge modules named by `challenges/*/comparator.json`. Negative controls
still fail: a `sorry` in another file, and an import of a Challenge.

**Remaining for L2.ASSEMBLY:** a fresh-checkout rebuild.

## D-48. The two-loop result complete: L2.ASSEMBLY closed

**Status.** Record; the author approved the fresh-checkout rebuild on
2026-11-18 ("go ahead").

**Fresh-checkout audit.** Commit 6940505 was cloned from GitHub and its
Mathlib taken from the cache. The steps ran from 17:05 to 17:30 UTC, niced on
three cores.

| Step | Result |
| --- | --- |
| `lake build` of `QED` | exit 0, 3,973 jobs, no warnings |
| Both Comparator Challenge and Solution pairs | build; only the 12 intentional Challenge `sorry` warnings (5 one-loop, 7 two-loop) |
| Frozen-anchor guard | OK |
| Module check | PASS: 600 Lean files, 2 Comparator configurations |
| HQ check | passed |
| ABI check | 144 of 144 frozen exports match the manifest |
| Axiom report | 51 theorems: every sealed theorem of the manifest and every Comparator theorem; all standard (propext, Classical.choice, Quot.sound) |

**Closure of the two-loop milestone.** With the headline (HV₃) sealed and
audited (D-46), its companion (HV₀) sealed (D-45), the enclosure (U₂) (D-39),
the two Comparator challenges accepted (D-47) and this audit, L2.ASSEMBLY is
done. The two-loop calculation is complete in the scope stated in the README
and D-44 item 1: the order-e⁵ 1PI vertex with on-shell one-loop counterterms,
A₁⁽⁴⁾ exact.

Deferred, and outside this milestone:
- the mass-dependent two-loop terms (D-36.2; Stage 0 of
  `docs/HIGHER-LOOP-PLAN.md`);
- the two-loop LSZ lift (D-44 item 1).

## D-49. Phase 5 rulings: targets, order of limits, value form, model extension (author ruling)

**Ruling.** On 2026-11-18 the author ruled on the design questions of
`docs/HIGHER-LOOP-PLAN.md` section 6, choosing the recommended option each
time.

1. **Targets.** Stage 0 comes first: the mass-dependent two-loop term
   A₂⁽⁴⁾(mₑ/m_μ) and A₂⁽⁴⁾(mₑ/m_τ). Then Stage 1a: the vacuum-polarization
   chain, sixth-order set (b).
2. **Order of limits (Q1).** The order of D-37 is kept:
   - ε → 0⁺;
   - then q² → 0⁺ at fixed regulators, uniformly over the on-shell pairs;
   - then (m_γ, Λ) → (0, ∞) jointly;
   - then the regulator fermions, last.

   With several lepton flavours, one threshold R_M covers the regulator pairs
   of every flavour.
3. **Form of the results (Q2, successor of D-36.3 for Phase 5).**
   - Exact closed constants where feasible, each with a companion certified
     enclosure theorem as for (U₂).
   - Otherwise a certified enclosure, labelled as such.
   - A flavour-dependent coefficient is stated as an explicit function of the
     mass ratio, with a separate enclosure on an input interval. Input
     uncertainty is never mixed into a coefficient.
4. **Model extension (Q3–Q5).**
   - The sealed anchors stay untouched.
   - The model is extended by minimal versioned successor packets, each with
     an embedding theorem into the frozen T1 model. These are physical
     flavours, each with its own Pauli–Villars pair (Stage 0), and later
     counterterms graded by order in e⁴ (Stage 2).
   - A family is a frozen structural predicate, proved equal to the
     relabelling orbit of explicit representatives.
   - The three frozen model generations are not unified now.

Questions Q6–Q8 were not asked separately. The plan's proposals are the
working defaults:
- **Q6, the amplitude:** the 1PI vertex.
- **Q7, normalizations:** 64π⁶[e⁶]F₂ and 16π⁴[e⁴]F₂, with mass ratio
  y = mₑ/m_ℓ.
- **Q8, completeness:** a family is reported as a subset.

They are settled only when the author approves the exact Lean text of the
corresponding declarations, as for every frozen statement.

## D-50. Phase 5 Stage 0 packet approved (author ruling)

**Ruling.** On 2026-11-18 the author approved the Stage 0 packet exactly as
written ("Approve as written"; confirmed "Approve all"). The packet has 29
declarations.

- **Flavour-successor model** (`QED.Lepton`), twelve declarations:
  - (F₀) `Flavors`, new;
  - (F₁)–(F₁₀): T1's flavour-dependent definitions (T₇), (T₈), (T₁₀),
    (T₁₁), (HV₁), (HV₂) over a general flavour type, with only the mass and
    weight lookups substituted; named `contractionAmplitude₂`,
    `regulatedAmplitude₂`, `contractionValue₂`, `onePIFunction₂`,
    `vertexOrderFive`, `IsVertexOrderFiveLimit`;
  - (F₁₁) `IsPhotonOnShell`, new: Π(0) = 0 for the vacuum polarization
    summed over all flavours, stated as a limit at lightlike k.
- **Lepton instance:** (L₀) `HeavyLepton` and (L₁) `leptonFlavors`. Each heavy
  lepton is a loop flavour block (m_ℓ, M₁ℓ, M₂ℓ) with weights (1, c₁ℓ, c₂ℓ),
  and the electron block is exactly T1's.
- **Coefficient:**
  - (U₃) `a2Four`: Passera eq. (10) at x = 1/y in real form, with every
    series argument in (−1, 1);
  - (U₃-alt) `a2FourPas` and the goal `a2FourPas_eq_a2Four`;
  - (U₃′) the limit y → 1;
  - (U₄) and (U₅): enclosures on the AKN Table 1 one-standard-uncertainty
    mass-ratio intervals.
- **Embedding:** (E₁)–(E₅). With the electron alone, the successor
  reproduces T1's 1PI function, vertex, limit predicate and photon condition,
  and the electron conditions do not depend on the flavours.
- **The headline (HM₂)**
  `QED.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit`, with
  `exists_heavyLepton_regulators`. Its structure is (HV₃)'s:
  - one threshold R_M for every regulator pair (D-49.2);
  - each heavy lepton's regulators lie above its mass and satisfy the two
    Pauli–Villars conditions at that mass;
  - the flavour-summed photon condition;
  - the conclusion ‖16π⁴F₂/e⁴ − (a1Four + Σ_ℓ a2Four(m/m_ℓ))‖ < η.

  The author thereby accepts the full multi-lepton form in place of the plan's
  per-lepton O3-M4. With no heavy lepton the statement is (HV₃); with μ and τ
  it is the full order-α² coefficient (Passera (13)).

The working defaults of D-49 (the 1PI vertex; 16π⁴[e⁴]F₂; y = mₑ/m_ℓ) are
confirmed by this approval.

**Review.** An independent refute-first statement review returned APPROVE
WITH NITS, and the nits were applied before approval:
- the copied bodies are identical to T1's apart from the stated
  substitutions;
- (F₁₁) is equivalent to Π(0) = 0 and fixes δ₃;
- `a2Four` matches Passera (10) term by term and numerically against
  Passera, AHKN and AKN;
- (HM₂) adds to (HV₃) only the heavy-lepton binders;
- the target is physically right, and the statement holds under the D-37
  order.

**Freeze.** The definitions are SEALED. The theorem goals are DRAFT_SORRY in
`QED/Frozen/Lepton/`, with providers in `QED/Provider/Lepton/`.

**Seals (2026-11-18).** Seven goals are sealed, each with body `by exact` its provider in
`QED/Provider/Lepton/`, from helpers in `QED/LeptonProof/Coeff*.lean`:
- `a2FourPas_eq_a2Four`;
- `tendsto_a2Four_one`;
- `a2Four_mem_muon` and `a2Four_mem_tau`, through `a2Four = a2Heavy`, which is definitional, and
  the O3-M3 enclosures;
- `exists_heavyLepton_regulators`;
- `onePIFunction₂_params` and `vertexOrderFive_params`, both `rfl`.

An independent refute-first seal audit returned PROVED for all seven. It found that only the
proof-body lines changed, the hashes and ABI match, the axioms are standard, there is no smuggled
hypothesis, the enclosure intervals and regulator witnesses are covered, and the guard and build
are clean. Six goals remain DRAFT_SORRY: the embedding theorems (E₂)–(E₅) and (HM₂).

**Seals (2026-11-18, continued).** The embedding theorems (E₂)–(E₅) are sealed, from helpers in
`QED/LeptonProof/Embed*.lean`:
- (E₂) `onePIFunction₂_relabel`, through a bijection of flavourings;
- (E₃) and (E₃′), by `Equiv.sumEmpty` and (E₂);
- (E₄) `isPhotonOnShell_leptonFlavors_zero_iff`, via (T₁₄) and (Z₇′): the lightlike limit is
  −Π(0)·k^μk^ν;
- (E₅) `onePIFunction₂_one_zero`: through order 3 every fermion field lies on the external line.

An independent refute-first seal audit returned PROVED for all five. Only (HM₂) remains
DRAFT_SORRY.

## D-51. The two-loop headline with heavy leptons (HM₂) sealed

**Status.** Record of a seal; no ruling.

On 2026-11-18 the frozen headline (HM₂)
`QED.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit`
(`QED/Frozen/Lepton/VertexOrderFiveLeptonPauliLimit.lean`; D-50) was sealed. Its provider is
`QED.Provider.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit`, and the proof is in
`QED/LeptonProof/HM*.lean`. The statement: for the order-e⁵ 1PI vertex with any finite family of
heavy leptons, 16π⁴F₂/e⁴ → A₁⁽⁴⁾ + Σ_ℓ A₂⁽⁴⁾(mₑ/m_ℓ), in the D-37 order with one regulator
threshold. With μ and τ this is the full order-α² coefficient of the 1PI vertex (Passera (13)).

**Proof route.**
1. Each heavy lepton's loop is written exactly as a weighted sum of T1 vertices at auxiliary
   regulator sets. These sets have masses (m, M_j, m_ℓ + M_ℓ1 + M_ℓ2) with
   M_j ∈ {m_ℓ, M_ℓ1, M_ℓ2}, and each satisfies T1's own Pauli–Villars conditions. The weights sum
   to 0 by the lepton's conditions.
2. The lepton vertex is therefore T1's vertex at a shifted photon counterterm, plus those sums.
3. The flavour-summed photon condition is equivalent to T1's (Z₈) at the shifted counterterm, so
   the sealed (HV₃) applies to the first part.
4. The heavy part, through T1's fixed-regulator q² → 0 machinery, is the heavy-lepton VP unit
   (`QED/Chain/HeavyVP*`), whose iterated limit is `a2Heavy`; and `a2Four = a2Heavy` by
   definition.

The auxiliary sets enter only at fixed regulators. No regulator limit is taken on them, so the
threshold R_M never has to exceed a physical lepton mass.

**Audit.** An independent refute-first seal audit returned PROVED, with no defects:
- the bytes, hashes and ABI match, and the provider type equals the frozen type;
- the closure of 73,408 constants uses only propext, Classical.choice and Quot.sound; it has no
  `sorryAx`, no `ofReduceBool`, no QED opaque or extern, and no `set_option`; `decide +kernel` is
  a kernel decision;
- (HV₃) is applied with its premises genuinely met;
- the weight identity is checked, the assembly misses no factor, the quantifier order is the
  frozen one, and the tolerance split is sound;
- the guard and the build are clean.

**Stage 0 is complete.** All 13 theorem goals of D-50 are sealed. Remaining Stage 0 hygiene:
- a Comparator challenge for (HM₂);
- a fresh-checkout audit.

The mass-dependent part of the Phase 4 exit criterion, deferred by D-36.2, is thereby met for
the 1PI vertex.

## D-52. Three-loop scope for the vacuum-polarization chains (author ruling)

**Ruling.** On 2026-11-19 the author approved this ruling with the Stage 1a packet (D-53), on
question Q4 of `docs/HIGHER-LOOP-PLAN.md` (option (a)). No frozen text changes.

The audit behind it found that T1's generic objects mean the right thing at L = 3:
- `Line.label`, `IsChord` and `loopCount`;
- `chordMomentum` and `lineMomentum₂`;
- the joint energy-first integral;
- the value, `fermionSign` and the 1/N!.

Each is backed by a proved helper generic in the loop count, or by a kernel check. The only
restrictions are in the docstrings of (T₁₀), (T₁₁) and (F₈). The ruling:

1. The source-facing scope of the joint energy-first value (T₁₀)/(F₇) extends to contractions
   with three or more loops in the following cases:
   - (a) the contractions of the vacuum-polarization chains (C₁) `QED.VPChain.IsVPChain n`, when
     summed in the family 1PI function (C₂) `QED.Lepton.onePIFamilyFunction₂` at
     K = 2n + 3, as in the chain vertex (C₃);
   - (b) each such chain contraction individually, in the integrability companion (HC₀), which
     states (T₉′) for the integrand of (T₁₀) directly at up to three loops.

   Both cases hold at ε > 0, with momentum conservation and the Pauli–Villars conditions.
2. Every proper divergent subgraph of a chain contraction is a one-loop vacuum polarization,
   renormalized by the model's single order-e² counterterm δ₃ (D-37.3). The overall
   logarithmic divergence of the vertex affects only F₁, and the headline concerns F₂.
3. The ruling covers (C₂) at K = 2n + 3, above the source-facing bound K ≤ 2nf + nA + 3 of
   (T₁₁)/(F₈), only for the chain family.
4. The full order-e^{2n+3} part of (T₁₁)/(F₈) for n ≥ 2 remains outside the scope and is not a
   renormalized amplitude.
5. Any later family (for example, set (c) as an enclosure) requires its own audit at its loop
   number and its own amendment of this ruling.

## D-53. Phase 5 Stage 1a packet approved: sixth-order set (b) (author ruling)

**Ruling.** On 2026-11-19 the author approved the Stage 1a packet exactly as written ("Approve as
written"). It has 13 declarations:
- **(C₁) `QED.VPChain.IsVPChain n`.** The vacuum-polarization chain with n insertions, each a
  two-vertex electron bubble or a `photonCt` (δ₃) vertex. It is spelled out as an explicit
  witness of the open line, the external photon on the middle vertex, and the photon walk.
  - n = 2 is set (b) with its δ₃ partners.
  - n = 1 is the Phase 4 VP class with its δ₃ class, checked by the kernel.
  - n = 3 is eighth-order I(a).
- **(C₂) `QED.Lepton.onePIFamilyFunction₂`.** (F₈)'s text with the filter `IsOnePI ∧ Fam`.
- **(C₃) `vertexChain` and (C₄) `IsVertexChainLimit`.** The chain vertex at order 2n + 3 and its
  ε → 0⁺ limit predicate.
- **(C₅) `a1SixSetB` = (8/3)ζ(3) − (4/135)π² − 943/324.** Its value is a proved integral
  (`QED/Chain/VPChainSetB*`). The literature pin is still open: Mignaco–Remiddi 1969 or
  Barbieri–Remiddi 1974.
  - Companions: (C₆), the enclosure 0.00255852 < a1SixSetB < 0.00255853, and (C₇), the
    integral representation.
- **Meaning theorems (M₁)–(M₄).**
  - (M₁): the family function with the trivial family is (F₈).
  - (M₂): the order-(2n+3) part splits into chain and non-chain.
  - (M₃): at T1's flavours the value is (T₁₀), by `rfl`.
  - (M₄): a three-loop set (b) contraction exists.
- **(HC₀) `jointEnergyFirstIntegrable_vertexChain_two`.** Every set (b) contraction has a
  genuinely integrable value integrand.
- **The headline (HC₃) `isFormFactorPair_vertexChain_two_pauli_limit`.** (HV₃)'s exact binders
  and quantifier order, at T1's flavours, with the conclusion ‖64π⁶F₂/e⁶ − a1SixSetB‖ < η. It is
  reported as a subset: set (b), 1 of 72 sixth-order diagrams, with its δ₃ counterterm graphs.

**Review.** An independent refute-first statement review returned APPROVE WITH NITS, and the nits
were applied before approval. It found:
- no false positive, false negative or double counting in (C₁), proved by hand from the frozen
  definitions, with kernel checks at n = 1;
- 9 relabelling orbits without automorphisms;
- (C₂) and (C₃) are mechanical diffs of (F₈) and (F₉);
- the L = 3 audit holds;
- (HC₃) is (HV₃) binder for binder; the normalization (α/π)³ = e⁶/64π⁶ is right; the existence
  clause cannot fail; the target is positive and non-vacuous.

The one-bubble analogue (HC₁) is a helper-level pilot, not an anchor.

**Seals (2026-11-19).** Six Stage 1a goals are sealed, each with body `by exact` its provider in
`QED/Provider/VPChain/`, from helpers in `QED/ChainProof/Quick*.lean`:
- (C₆) `a1SixSetB_bounds` and (C₇) `integral_chainTwo_eq_a1SixSetB`, through `a1SixSetB = aSetB`
  by `rfl` and the T2 helpers;
- (M₁) `onePIFamilyFunction₂_true`;
- (M₂) `onePIFunction₂_sub_eq_family_add`, proved with `IsVPChain n` ⇒ total order 2n + 3 via the
  photon-field bijection;
- (M₃) `contractionValue₂_params`, by `rfl`;
- (M₄) `exists_isVPChain_two`, by a kernel check of the bubble–bubble representative.

An independent refute-first seal audit returned PROVED for all six. (HC₀) and (HC₃) remain
DRAFT_SORRY.

**Seal of (HC₀) (2026-11-19).** `jointEnergyFirstIntegrable_vertexChain_two` is sealed with body
`by exact QED.Provider.VPChain.jointEnergyFirstIntegrable_vertexChain_two`.
- The eight one- and two-loop representatives were already integrable (`QED/ChainProof/RepsInt*`).
- The bubble–bubble representative is the only three-loop one. It is handled by a common complex
  rotation of the three loop energies (`QED/Integration/ThreeLoopRotation.lean`). On the rotated
  contour every denominator is elliptic, and each Pauli–Villars-summed bubble decays like ρ⁻⁵, which
  gives joint integrability on (ℝ⁴)³ (`QED/ChainProof/RepsIntBB*.lean`). No mass condition is used.
- An independent refute-first seal audit returned PROVED: statement bytes and ABI unchanged,
  binder convention D-13, all nine representatives discharged, standard axioms only.

**Seal of (HC₃) (2026-11-19).** `isFormFactorPair_vertexChain_two_pauli_limit` is sealed with body
`by exact QED.Provider.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`.
- The provider applies `isFormFactorPair_vertexChain_two_pauli_limit_of_classLinks` to
  `QED.ChainProof.chainClassLinks` (`QED/ChainProof/HCFinal.lean`). That is `classLinks_of_reps`
  on the limit, nested value and covariance of the bubble–bubble representative
  (`QED/ChainProof/HCBB2*.lean`) and of the bubble-on-side representatives
  (`QED/ChainProof/HCSideBD*.lean`).
- An independent refute-first seal audit returned PROVED: statement bytes and ABI unchanged,
  provider type definitionally the frozen statement, every input proved, no vacuity, standard
  axioms only.

All thirteen Stage 1a goals are sealed. The sixth-order set (b) coefficient is proved: 64π⁶F₂/e⁶
tends to `a1SixSetB` = 8/3·ζ(3) − 4/135·π² − 943/324 ≈ 0.00255852 in the D-37.4 order.

## D-54. Three-loop programme: exact target and four-loop readiness (author ruling)

**Author rulings (2026-11-19).**
1. **Scope and order.** Complete sets (a), (b) and (c) of the sixth-order coefficient, then attack sets
   (d) (light-by-light, 6 diagrams) and (e) (no fermion loops, 50 diagrams) analytically, reducing
   them as far as possible.
2. **Exact target.** Every analytic result that Laporta and Remiddi (1996; source
   `laporta-remiddi-1996`) prove or use is to become an analytic Lean theorem, and their closed form
   of A₁⁽⁶⁾ is to be reproduced in full. Certified numerics are at most an interim step, and any
   interim enclosure states its width.
3. **Four-loop readiness.** The three-loop work must serve as input to a later four-loop
   computation:
   - counterterms graded generically in the loop order;
   - per-set theorems that expose the reusable objects, such as the two-loop vacuum polarization
     Π⁽⁴⁾(q²) for all q² and the renormalization constants;
   - general analytic machinery (integration by parts, master integrals, a polylogarithm library)
     preferred over set-specific tricks.
4. **Two-loop enclosure.** The numerical check of A₁⁽⁴⁾ is to be tightened beyond the published nine
   digits.
5. **Overnight mode.** The author pre-authorized continued work on the exact three-loop programme in
   overnight mode: statements are frozen provisionally, pending approval in the morning.

**Choices made overnight, approved by the author on 2026-11-19.** These follow the analytic-route
memo's recommendations.
- **(P1)** Non-integer dimension may be used as an evaluation device only. The model is unchanged,
  and a proved bridge theorem per set links the model's limit to the dimensionally continued
  expression. This would be a successor note to D-36.1.
- **(P2)** Large polynomial identities, such as integration-by-parts reduction certificates, are
  checked in the kernel by `decide +kernel`. This is read as within D-34.
- **(P3)** Theorems are stated per gauge-invariant set, not per graph, so that each statement is
  free of infrared divergences.

The memo rates a fully analytic end-to-end proof of the Laporta–Remiddi closed form at 5–10%, and the
reusable layers (dimensionally continued integrals, integration-by-parts certificates, the
polylogarithm library) at 35–55%. Pilots run first: the triple-cross integral J₀ in four dimensions,
and the set (a) value integral.

## D-55. Counterterms on non-electron flavours (finding; ruling superseded by D-55 revised)

**Finding (2026-11-19).**
- **The frozen models.** Neither flavouring definition (`QED/Frozen/WickModel/Flavoring.lean`,
  `QED/Frozen/Lepton/Flavoring.lean`) lets a counterterm vertex (δ₁, δ₂, δm) sit on a non-electron
  line. Flavour is constant along a closed loop, so loops of regulator fermions or heavy leptons
  never carry counterterms.
- **Order e⁵ and the chains are unaffected.** At order e⁵ and on the vacuum-polarization chains, no
  counterterm can sit on a closed loop. (HV₃), (HM₂), (HC₀) and (HC₃) are therefore correct as
  stated, and no frozen anchor needs a successor. This strengthens D-52.4.
- **Order e⁷ is affected.** In the two-loop vacuum polarization of a regulator flavour (set (a)),
  the mass subdivergence of the internal self-energy is not renormalized. This leaves a term in
  A₁⁽⁶⁾ of about −(1/30)·Σ_f c_f (m/M_f)² ln(Λ²/M_f²). It grows without bound as Λ → ∞ at fixed
  M_f, so the D-37 limit would not exist. A muon loop diverges the same way.
- **Numerical evidence.** The memo's script confirms the mass shift to 10⁻⁷. The residue grows
  linearly in ln Λ with the predicted slope, and after the predicted term is subtracted the remainder
  is constant to six figures.

**Provisional ruling (overnight mode; superseded by D-55 revised, approved with D-57).** In the Stage 2 successor every
flavour gets its own on-shell counterterms. Flavour f's conditions are the electron's with the open
line set to f, and δ₃ is shared by all flavours. The frozen models are unchanged.

## D-56. Three-loop target constant and sharpened enclosures (author ruling)

**Ruling.** On 2026-11-19 the author approved the three declarations as frozen ("yes, approve D-54
and D-56 too"), together with the D-54 choices P1–P3. The manifest entries move from approval
version "provisional" to "1".

**Provisional freeze (2026-11-19, overnight mode).** Three declarations implement D-54.2 and D-54.4:
- **(R₁) `QED.ThreeLoop.a1SixLR`** (`QED/Frozen/ThreeLoop/A1SixLR.lean`), a definition: the
  Laporta–Remiddi closed form of A₁⁽⁶⁾ (LR96 abstract and eq. (5); Passera eq. (14)). ζ(3), ζ(5) and
  a₄ = Li₄(1/2) are written as explicit series. It fixes the target of the three-loop headline. That
  the model's coefficient equals it is not yet proved.
- **(R₂) `QED.ThreeLoop.a1SixLR_bounds`**: 1.1812414565871995 < a1SixLR < 1.1812414565872003.
- **(U₂′) `QED.TwoLoop.a1Four_bounds_fine`**: −0.32847896557919380 < a1Four < −0.32847896557919376,
  sixteen significant digits. Passera eq. (9) prints seventeen, so this sharpens (U₂) to about the
  published precision; it does not go beyond it.

**Review.** An independent refute-first review returned APPROVE WITH NITS.
- It checked every coefficient of (R₁) against both versions of LR96 and Passera (14).
- It confirmed that the series are summable and denote ζ(3), ζ(5) and Li₄(1/2).
- It confirmed the value 1.18124145658720000627… to 50 digits, and that the decimal literals
  elaborate as the intended rationals.
- Its two docstring digit corrections and its fuller quotation of Passera (9) are applied.

The manifest records these entries with `approval_version` "provisional".

**Seals (2026-11-19).** (R₂) and (U₂′) are sealed with bodies `by exact` their providers in
`QED/Provider/ThreeLoop/` and `QED/Provider/TwoLoop/`, from the helpers `QED/Polylog/A1Six.lean`
and `A1FourFine.lean`. An independent refute-first seal audit returned PROVED: statement bytes
and ABI unchanged, provider types definitionally the frozen statements, tail bounds genuine,
standard axioms only. All three were later approved by the author (ruling above).

**D-55 revised (2026-11-19, overnight; approved by the author with D-57).** Drafting the Stage 2 statements
showed that the literal per-flavour scheme fails. Under the frozen value prescription each
contraction is integrated separately, flavour-summed inside its integrand. With an independent δ₂
on every flavour, a counterterm contraction on a closed loop then decays only like |ℓ⃗|⁻¹, so it is
not integrable and its value defaults to 0. A numerical check confirmed the slopes and verified the
alternative.

**Revised provisional ruling (S2′).**
- Each physical lepton block (lepton plus its two regulator fermions) carries one set of
  counterterm coefficients d₁, d₂, d_m, fixed on shell at the lepton's physical mass.
- On a regulator line the mass counterterm vertex is d_m·M_f, with the regulator's own mass.
- δ₃ is shared by all flavours.

**What the check showed.**
- **Integrability.** Under S2′ the counterterm contraction decays like |ℓ⃗|⁻⁵ (|ℓ⃗|⁻⁶ for the 00
  component), so the block's two Pauli–Villars conditions suffice. With d_m·m in place of
  d_m·M_f it decays only like |ℓ⃗|⁻³.
- **Limit.** The regulator residue of set (a) is independent of Λ and vanishes as M → ∞. Set (a)
  tends to 0.052870652475767.
- **Pole masses.** The muon and tau poles stay at their physical masses.

**Open risk.** It is not yet tested whether the genuine two-loop vacuum polarization of a block is
integrable with only two Pauli–Villars conditions.

## D-57. Phase 5 Stage 2 packet approved: the graded counterterm model (author ruling)

**Ruling.** On 2026-11-19 the author approved the packet as frozen ("approved, continue"), with the
answers to Q1–Q6 recorded below (Q1: S2′, so D-55 revised is approved with it) and the level-0
form of (X₀). The manifest entries move from approval version "provisional" to "1".

**What was frozen (2026-11-19, overnight, at the author's instruction).** 43
declarations in namespace `QED.Graded`, one per file under `QED/Frozen/Graded/`, with manifest
`approval_version` "provisional". They are 25 definitions (SEALED) and 18 theorem goals (DRAFT_SORRY;
quarantined providers under `QED/Provider/Graded/`). The design note, with the binder tables, risk
analysis and the record of both reviews, is [STAGE2-DESIGN.md](STAGE2-DESIGN.md).

**The model.**
- Counterterms graded by loop level: `Counterterms` stores e-free coefficients d₁, d₂, d_m per
  flavour and d₃, per level k, entering at order e^{2(k+1)}, so order separation is definitional.
- The counterterm scheme follows D-55 revised (S2′). `IsRenormalizedThrough` takes the scheme map
  `rep` as a parameter, and `leptonRep` gives S2′: shared coefficients per lepton block, with δm·M_f
  on regulator lines and δ₃ shared.
- The order-by-order on-shell conditions (`IsOnShellAt`, `IsChargeNormalizedAt`,
  `IsPhotonOnShellAt`) reduce to the frozen one-loop and two-loop conditions at level ≤ 1.

**The goals.**
- Existence and uniqueness of the level-0 and level-1 counterterms.
- Embedding into the frozen two-loop and lepton models: 1PI parts, the connected part (E-G₅), and
  the level-one condition equivalences.
- The reusable two-loop vacuum polarization limit with the leptons, for s > −4m² (R-Π₄).
- The order-e⁵ integrability companion (X₀).
- The exit test `isSpinFormFactorPair_lszFive_lepton_pauli_limit`, the D-44.1 lift of (HM₂)
  through LSZ.

**Reviews.**
- Two independent refute-first reviews, the full packet and then the changes, both returned
  APPROVE WITH NITS, and every nit was applied.
- The freezer wrote declaration text byte-identical to the reviewed candidates (43/43), and every
  file elaborates.
- The per-block Pauli–Villars hypotheses are standing assumptions on the regulator data, not proof
  obligations.

**Questions put to the author (answered as listed by the approval).**
- Q1, S2 versus S2′: provisionally S2′ (D-55 revised).
- Q2: `rep` stays a parameter.
- Q3: the existential limit for Π⁽⁴⁾ is stated now.
- Q4: the exit test is about form factors only; the Landé and wave-packet clauses come later.
- Q5: one common lower bound m₀ on the masses.
- Q6: D-54.3 asks for Π⁽⁴⁾(q²) for all q², but (R-Π₄) covers s > −4m²; the timelike region above
  threshold is deferred.
- (X₀) constrains only level-0 data, because level ≥ 1 counterterms enter only tree contractions at
  order e⁵.

**Open risk.** Integrability of the genuine two-loop vacuum polarization of a block is argued by
power counting (it needs only Σc = 0), but not yet checked numerically.

**Seals (2026-11-19).** Eight goals are sealed with bodies `by exact` their providers in
`QED/Provider/Graded/`, proved in `QED/GradedProof/`:
- `selectedPart_eq_pow_mul` and `selectedPart_congr` (order homogeneity);
- `isPhotonOnShellAt_one_iff`, `isChargeNormalizedAt_one_iff` and `isOnShellAt_one_iff` (the
  level-one conditions are the frozen ones);
- `vertexPart_two_eq` (the order-e⁵ vertex: the frozen vertex plus the level-1 charge counterterm
  tree);
- `onePIPart_eq_onePIFunction₂_sub` and `connectedPart_eq_connectedFunction_sub` (embedding into
  the frozen two-loop model; the key lemma is that a counterterm on a closed fermion cycle costs one
  extra loop, two in a 1PI graph).

Checks: the frozen bytes changed only in the proof bodies; ABI unchanged (8/8); standard axioms; the
guard is OK. An independent refute-first seal audit found all eight PROVED: provider types are
definitionally equal to the frozen ones with D-13 binders, and no draft anchor or provider is
reachable.

**Seals, continued (2026-11-19).** Two more goals are sealed the same way:
- `existsUnique_withLevel_zero`: the level-0 counterterms exist and are unique for any idempotent
  `rep` with block Pauli–Villars data. The photon counterterm uses a new block split of the flavour
  sum into single-lepton photon functions (`QED/GradedProof/LevelZeroPhotonSplit.lean`).
- `d₁_eq_d₂_zero`: the level-0 Ward identity, from the sealed one-loop identity.

ABI unchanged (2/2); standard axioms; guard OK. An independent seal audit found both PROVED.

**Seal of (G-Σ₂) (2026-11-19).** `selfEnergyPart_two_existsUnique` is sealed with body `by exact`
its provider. The proof (`QED/GradedProof/SE2*.lean`) has three clauses:
- integrability of every order-4 1PI term, by reduction to eight classes;
- the covariant limit `A p̸ + B M` below threshold with unique `(A, B)`, from explicit parametric
  limits, reflection covariance and null-ray continuity;
- differentiability of `A(−z²)z + B(−z²)M_f` at `z = −M_f`, by differentiation under the integral
  along lines through the origin. Only differentiability is proved, not analyticity.

Standard axioms; guard OK. An independent seal audit found it PROVED. (Correction: this note
originally said "ABI unchanged"; the ABI hash in fact moved. See the ABI note below.)

**Seal of (G-Π₂) (2026-11-19).** `vacuumPolarizationPart_two_existsUnique` is sealed with body
`by exact` its provider. The proof (`QED/GradedProof/VP2*.lean`) has two clauses:
- integrability of every order-4 1PI term, by reduction to seven classes and divided differences
  over each lepton block;
- the transverse limit `Pol(k·k)(k·k g − k k)` on `s > −4m₀²` with unique `Pol`. The classes are
  grouped so that each group satisfies the Ward identity in the limit: the vertex-counterterm
  classes through the one-loop limit, the fermion-counterterm classes through a one-loop Ward
  identity, and the three two-loop classes through a two-loop Ward identity whose six pinched
  terms cancel in pairs under unimodular changes of loop momenta.

Standard axioms; guard OK. An independent seal audit found it PROVED.

**ABI hashes move on sealing (author ruling, 2026-11-19).** Sealing makes a frozen anchor import
its provider, so the frozen statement is elaborated with the provider's transitive imports in
scope. For (G-Σ₂) and (G-Π₂) this changes one instance in the elaborated statement: ℂ's
`NormedCommRing` is found as `CommCStarAlgebra.toNormedCommRing ℂ instCommCStarAlgebraComplex`
instead of `NormedField.toNormedCommRing ℂ Complex.instNormedField`. This is the only difference
in the `pp.all` text (diffed for both goals). The two instances are equal by
`with_reducible_and_instances rfl`, and an independent audit had the kernel accept the approved
statement with the sealed constant as its proof and the reverse. The change is therefore
semantics-neutral. Ruling: record each such move with its diff and the definitional-equality
check, and update `abi_sha256` in the manifest. Updated: `selfEnergyPart_two_existsUnique`
`13a3890f…` → `aa21aa23…`; `vacuumPolarizationPart_two_existsUnique` `c24e9c2f…` → `471919e7…`.
Every later seal runs `scripts/frozen_abi.py --check` in full and handles any move this way.

**Seal of (X₀) (2026-11-19).** `jointEnergyFirstIntegrable_connectedPart_five` is sealed with body
`by exact` its provider. Every attached, connected (1,1) contraction at graded order 5 satisfies
(T₉′) for every ε > 0, with no bound on the masses. The proof (`QED/GradedProof/X0*.lean`) splits
by grading and loop count:
- nonzero gradings leave only trees;
- one loop: generic mass-free one-loop integrability through an auxiliary loop with a fourth-power
  propagator, and block sums over closed fermion loops, where mass entries come in even number
  around the loop;
- two loops: a generic power-counting criterion for open contractions, products of one-loop
  pieces when the loops share no line, and block sums with padding otherwise.
Coverage is checked in the kernel by enumeration over normal forms, one `decide +kernel` theorem
per pairing (each under 4 GB). ABI unchanged; standard axioms; guard OK. An independent seal
audit found it PROVED, including the coverage of the enumeration.

**Seal of (G-ex₂) (2026-11-19).** `existsUnique_withLevel_one` is sealed with body `by exact` its
provider: given the level-0 data renormalized through e², exactly one level-1 counterterm set
renormalizes through e⁴. The renormalization conditions are affine in the level-1 data with
nonzero coefficients; the solution is real because the order-e⁴ on-shell self-energy data, the
vacuum polarization at s = 0 and the order-e⁵ vertex at q = 0 are real. Reality comes from a
conjugate-linear map fixing every gamma matrix (`SE2Real*`, `VP2Real*`, `V5ZeroSharp*`); the
general-flavour vertex splits into one-electron vertices with loop flavours allowed lighter than
the open line (`V5Zero*`). ABI unchanged; standard axioms; guard OK; independent seal audit PROVED.
Binder note: the provider's `hm₀ : 0 < m₀` default resolves `m₀` by name in the caller's
context (it also requires a hypothesis `∀ g, _ ≤ Φ.mass g`), since a plain `by assumption`
would pick `0 < P.Λ`; the binder's type is exactly the frozen one, and the audit
confirmed it affects elaboration only.

**Seal of (WI₂) (2026-11-20).** `d₁_eq_d₂_one` is sealed with body `by exact` its provider: at
level 1 the charge and wave-function counterterms agree, for every flavour. Route
(`QED/GradedProof/WI2*.lean`): a parametric Ward–Takahashi identity at zero momentum transfer
(the derivative of a parametric value along the external momentum is minus the sum of its
zero-momentum insertions), applied class by class to the order-e⁴ self-energy
R + X − V + F + P0 + P1 + C1 + C2 (C by one-loop closed forms) and matched to the order-e⁵ vertex
classes at q = 0 (the vacuum-polarization class by charge conjugation, the Furry pair removed);
the flavour split; then the on-shell and charge conditions give d₁ = d₂. ABI unchanged; standard
axioms; guard OK; independent seal audit PROVED.
Binder note (deviation from D-13, recorded): the provider's hypothesis defaults are
`by with_reducible assumption`, because plain `by assumption` unfolds the on-shell predicates at
the wrong order and times out. Each binder's type is exactly the frozen one, and the audit
confirmed the seal passes each frozen hypothesis to its own slot.

**Seal of (X₁) (2026-11-20).** `isLSZAmplitudePart_five_self` is sealed with body `by exact` its
provider: the order-e⁵ LSZ amplitude at `(p, p)` exists and is 0. Route
(`QED/GradedProof/X1*.lean`): the order-e⁵ Dyson decomposition of the connected three-point
function at fixed ε (`X1C`: gluing and routing of contractions, value factorization, tadpoles
vanish by a γ₅ sign argument, and the counting by peeling one 1PI piece at a time off the in-leg,
the out-leg and the photon, with the graph theory of cuts; `peelV_dysonFive`), the off-shell
limits of the vertex parts (`X1D`, `X1E`), the photon legs near q = 0 (`X1E`), and the
assembly (`X1F.isLSZAmplitudePart_five_self_of_dysonFive`). ABI unchanged; standard axioms;
guard OK; independent seal audit PROVED.
Binder note: the provider's `hm₀ : 0 < m₀` default resolves `m₀` by name in the caller's
context, as for (G-ex₂); each binder's type is exactly the frozen one, and the audit confirmed each frozen
hypothesis goes to its own slot.

**Seal of (X₂) (2026-11-20).** `isSpinFormFactorPair_lszFive_lepton_pauli_limit` is sealed with
body `by exact` its provider: with the order-e⁵ LSZ amplitude in place of the 1PI vertex, the
lepton-flavour Pauli limit at order α² holds with target A₁⁽⁴⁾ + Σ A₂⁽⁴⁾(m/m_ℓ). Route
(`QED/GradedProof/X2*.lean`): on shell the amplitude is the order-e⁵ vertex sandwich plus a γ
term plus κ times the order-e³ vertex sandwich, with κ = q² D(q²) Pol₁(q²) → 0 as q² → 0 at fixed
regulators (`lszFive_eq`, `exists_kappa_small`); the vertex term is the sealed (HM₂) limit through
(E-G₃) at η/2 and the κ term is bounded through the one-loop Pauli limit; the order-e⁵ Dyson
decomposition is used only at renormalized points with positive regulators, where
`X1C.peelV_dysonFive` supplies it (`X2Seal`). ABI unchanged; standard axioms; guard OK;
independent seal audit PROVED.

## D-58. Phase 5 Stage 3a/3b packet: sets (a) and (c) (provisional freeze; author approval pending)

**Provisional freeze (2026-11-21, overnight mode under D-54.5).** The statement packet for sets (a)
and (c) of the sixth-order coefficient is frozen provisionally. The author has not yet approved it.
The manifest records each entry with `approval_version` "provisional". There are 30 declarations,
one per file:
- 13 definitions (SEALED, imported by `QED.lean`);
- 17 theorem goals (DRAFT_SORRY), with quarantined provider stubs under `QED/Provider/Graded/` and
  `QED/Provider/ThreeLoop/`.

The design memo is the Stage 3a/3b packet memo (session scratch, `stage3pkt/PACKET-3A-3B.md`). The
frozen declaration text is byte-identical to the reviewed candidates with the fixes below applied
(30/30).

**Generic declarations (namespace `QED.Graded`, `QED/Frozen/Graded/`).**
- (Gf₁) `familyVertex`: the order-K vertex of a selected family of graded contractions, (G₈ᵥ)'s
  text with a selection in place of the 1PI filter. (Gf₂) `IsFamilyVertexLimit`: its ε → 0⁺ limit.
- (Gs₁) `selfEnergySelPart`, (Gs₂) `IsOnShellSelAt`, (Gs₃) `IsChargeNormalizedSelAt`: (G₈ₛ), (G₉)
  and (G₁₀) for a selected family. They define a family's share of the level-1 counterterms.
- Goals: (MF₁) `familyVertex_isOnePI`, (MS₁) `isOnShellSelAt_isOnePI_iff` and (MS₂)
  `isChargeNormalizedSelAt_isOnePI_iff` (with the 1PI selection these are the Stage 2 objects);
  (E-G₄) `familyVertex_isVPChain_two`, the bridge from the graded set (b) family vertex to the
  frozen chain vertex (Stage 2 deferred item D1).

**Set (a) (namespace `QED.ThreeLoop`, `QED/Frozen/ThreeLoop/`).**
- (A₁) `IsSetA`: the one-loop vertex with one single-loop insertion on its photon.
- (A₂) `a1SixSetA`: the closed form of Kaptari, Lashkevich and Solovtsova (2025), eq. (16), first
  obtained by Mignaco and Remiddi (1969), ≈ 0.0528706524758.
- Block K: (A₄) `ksRhoFour`, the Källén–Sabry spectral function (Kaptari et al. eq. (20)), and
  (A₅) `piHatFour`, the renormalized fourth-order vacuum polarization as a dispersion integral.
- Goals: (A₃) `a1SixSetA_bounds`; (A₇) `integral_piHatFour_eq_a1SixSetA`; (MA₁) `exists_isSetA`;
  (MA₂) `not_isSetA_and_isVPChain_two`; (HA₀) `jointEnergyFirstIntegrable_setA`; and the headline
  (HA₆) `isFormFactorPair_vertexSetA_pauli_limit`: 64π⁶F₂/e⁶ tends to `a1SixSetA` in the D-57
  order of limits, at the electron block with no heavy lepton, with counterterms renormalized
  through order e⁴ in `leptonRep`.

**Set (c) (namespace `QED.ThreeLoop`, `QED/Frozen/ThreeLoop/`).**
- (Sc₁) `IsVPSelfEnergy`: the one-loop self-energy with a bubble or a `photonCt` on its photon.
- (Sc₂) `IsVPShareOnShell`: the vacuum-polarization share s of the level-1 counterterms, fixed by
  the family-restricted on-shell and charge conditions.
- (Sc₃) `IsSetC`: one vacuum-polarization element in the fourth-order vertex, with its
  counterterm graphs.
- (Sc₄) `a1SixSetC`: Barbieri–Remiddi (1974) eq. (3), ≈ −0.1501722821.
- Goals: (Sc₅) `a1SixSetC_bounds`; (G-ex-s) `existsUnique_isVPShareOnShell`; (WI-s)
  `isVPShareOnShell_d₁_eq_d₂`; (MC₁) `exists_isSetC`; (MC₂) `isSetC_disjoint`; (HS₀)
  `jointEnergyFirstIntegrable_setC`; and the headline (HS₆)
  `isFormFactorPair_vertexSetC_pauli_limit`: as (HA₆), with the level-1 fermion counterterms
  replaced by every VP share s, and target `a1SixSetC`.

**Goals already proved in scratch.** Eight goals have sorry-free proofs in the packet's scratch
check files: (A₃), (Sc₅) and (A₇) (from the helpers `QED.Chain.aSetA_bounds`,
`aSetC_bounds` and `integral_setA_eq_aSetA`, by `rfl` on the constants); (MF₁), (MS₁) and (MS₂)
(by `rfl` and `Iff.rfl`); (MA₁) and (MC₁) (by `decide +kernel` on representatives). They are
frozen as DRAFT_SORRY all the same. Each is sealed separately, after a seal audit.

**Source pin.** Kaptari, Lashkevich, Solovtsova, Phys. Rev. D 112 (2025) 073008,
arXiv:2508.05119v1, is pinned as `kaptari-lashkevich-solovtsova-2025` (370716 bytes, sha256
`ce2b08a15c91be594c6e06780cecaec2b8c54bfb0e01dd23c2a169a45c699f1a`) in `sources/manifest.json` and
[SOURCES.md](../SOURCES.md). The PDF is kept only in the ignored cache.

**Review.** One independent refute-first review returned APPROVE WITH FIXES. It checked the
counts with its own graph enumerator and the constants with high-precision numerics, including
the dispersive form of the set (a) integral. All six fixes are applied:
1. **(HS₀) was false as stated** (blocking). The candidate quantified over every contraction in
   (Sc₃), including ones that are not 1PI. It now has the hypothesis `hC₁ : IsOnePI C`, and its
   docstring says "every 1PI contraction".
2. **The Kaptari source was not pinned** (blocking). It is now pinned (above), and the (A₂) and
   (A₄) docstrings cite arXiv:2508.05119v1 and the source id.
3. **The (Sc₃) count was wrong.** Set (c) has 39 graphs and 56 relabelling orbits: each of the 17
   graphs with a `photonCt` vertex gives two orbits, one per field pairing. The list of excluded
   graphs now says that a closed loop with more than two vertices belongs to set (d) or is a Furry
   graph (or, as the two-loop vacuum polarization in the one-loop vertex, to set (a)).
4. **(E-G₄) overstated its role.** It is one of the bridges; adding (HC₃) to the graded headlines
   also needs the flavour relabelling (E₃) and the meaning theorems (E-G₂).
5. **Label clash.** The set (c) labels (C₁)–(C₅) clashed with the frozen Stage 1a labels. They
   are renamed (Sc₁)–(Sc₅) in the docstrings; no Lean name changed.
6. **(Sc₄) described the graphs loosely.** It now says the 12 graphs come from the six
   fourth-order vertex graphs without a fermion loop.

**Open questions for the author (provisional answers are the packet's recommended defaults).**
- Q1 (Q-a1): the set (a) headline is stated at n = 0 heavy leptons (electron block only).
- Q2 (Q-a2): set (a) owns the level-1 photon counterterm d₃(1).
- Q3 (Q-a3): the Källén–Sabry identification (R-KS) is not frozen; it stays inside the proof. The
  optional block K ((A₄), (A₅), (A₇)) is frozen, at the freeze instruction's request. The memo
  itself recommended not freezing block K unless the author wants a physical anchor for Π⁽⁴⁾. The
  author may want to drop these three files.
- Q4 (Q-c4): both headlines assume renormalization "through 2" (order e⁴), not "through 1".
- Q5 (Q-c5): the set (b) bridge (E-G₄) is frozen now.
- Q6 (Q-ns): generic declarations in `QED.Graded`, set-specific ones in `QED.ThreeLoop`.
- Q7 (Q-c6): the orbit counts (9 for set (a); 39 graphs and 56 orbits for set (c)) stay proof
  obligations of the enumeration step, not frozen goals.
- Q8 (new): the renamed labels (Sc₁)–(Sc₅) do not match the (Sc) numbering of
  [SETC-KERNEL-PLAN.md](SETC-KERNEL-PLAN.md), where (Sc₁) is `IsSetC` and (Sc₅) is the constant.
  The plan is not changed. Should the plan be renumbered to match, or the labels changed again?

**Seal of the eight proved D-58 goals (2026-11-21).** Eight of the 17 D-58 goals are sealed with
body `by exact` their providers. The frozen statements stay provisional with the rest of D-58;
sealing does not approve them. Each provider takes the D-13 binder convention (data implicit;
none of the eight has a hypothesis) and imports no draft anchor or quarantined provider:
- (A₃) `a1SixSetA_bounds` and (Sc₅) `a1SixSetC_bounds`: the frozen constants (A₂) and (Sc₄)
  unfold to the helper constants `QED.Chain.aSetA` and `QED.Chain.aSetC`, whose enclosures
  `QED.Chain.aSetA_bounds` and `QED.Chain.aSetC_bounds` (`QED/Chain/SetAConst.lean`,
  `SetCConst.lean`) are the providers' proofs.
- (A₇) `integral_piHatFour_eq_a1SixSetA`: (A₄), (A₅) and (A₂) unfold to the helper `ksRho`,
  `piHat4` and `aSetA`, and the identity is `QED.Chain.integral_setA_eq_aSetA`
  (`QED/Chain/SetAValue.lean`).
- (MF₁) `familyVertex_isOnePI` by `rfl`; (MS₁) `isOnShellSelAt_isOnePI_iff` and (MS₂)
  `isChargeNormalizedSelAt_isOnePI_iff` by `Iff.rfl`.
- (MA₁) `exists_isSetA` and (MC₁) `exists_isSetC`: representatives of seven gauge vertices,
  defined in the providers and checked by `decide +kernel` through the decision procedures of
  `QED.TwoLoop.Enumeration`. For set (a), the one-loop vertex with the vertex-type two-loop
  bubble on its photon (open line `y → 0 → 1 → 2 → x`, loop `3 → 4 → 5 → 6`); for set (c), the
  two-loop ladder with the one-loop bubble on its outer photon (open line
  `y → 4 → 3 → 2 → 1 → 0 → x`, bubble `5 ⇄ 6`). The set (c) representative has no counterterm
  vertex, so (Sc₃) holds for every grading.

Checks: the frozen bytes changed only in the eight proof bodies; the module and provider builds
exit 0 with no warnings; standard axioms only (8/8); ABI unchanged (8/8, recomputed for these
exports with the `frozen_abi.py` method; the full `frozen_abi.py --check` passes); guard OK.
Independent seal audit (refute-first, 2026-11-21): all eight PROVED, APPROVE-FOR-AUTHOR. It
checked the frozen diff (eight body lines and eight state lines only), provider types equal to
the frozen types up to D-13 binder information, a fresh elaboration of each statement, standard
axioms for anchors and providers, quarantine (no draft or provider import), and non-vacuity (the
constants are definitionally the helper constants, (A₇) uses the frozen `piHatFour`, and both
representatives are genuine three-loop graphs of their sets). Non-blocking: the frozen docstrings
of (A₇) and `a1SixSetA` name an internal helper; the guard's file scan also walks `.scratch/`,
which can race with a concurrent export copy (a false alarm, not a seal defect).

**Seal of four further D-58 goals (2026-11-21).** Four more of the 17 D-58 goals are sealed with
body `by exact` their providers, bringing the sealed D-58 goals to 12. The frozen statements stay
provisional with the rest of D-58; sealing does not approve them. Each provider takes the D-13
binder convention (data implicit, hypotheses `by assumption` auto-parameters), applies a tracked
helper with exactly the frozen statement, and imports no draft anchor or quarantined provider:
- (MA₂) `not_isSetA_and_isVPChain_two` ← `QED.ChainProof.SetALink.not_isSetA_and_isVPChain_two'`
  (`QED/ChainProof/SetALinkDisjoint.lean`): (A₁) and (C₁) fix the same open line, and the second
  chain insertion has no admissible starting vertex.
- (MC₂) `isSetC_disjoint` ← `QED.ChainProof.SetCLink.isSetC_disjoint`
  (`QED/ChainProof/SetCLinkDisjoint.lean`): with (A₁) or (C₁), every clause of (Sc₃) leaves
  graded order at most 5, not 7.
- (G-ex-s) `existsUnique_isVPShareOnShell` and (WI-s) `isVPShareOnShell_d₁_eq_d₂` ←
  `existsUnique_isVPShareOnShell_c` and `isVPShareOnShell_d₁_eq_d₂_c`
  (`QED/ChainProof/SetCLinkFinal.lean`): the block Pauli–Villars conditions give the total ones,
  and the self-energy, vertex and Ward inputs of `SetCLinkShareAlg` hold. The renormalization
  hypothesis `hD` is passed but not used by the helper.

Binder note: in (G-ex-s) and (WI-s) the provider's `hm₀ : 0 < m₀` default resolves `m₀` by
name in the caller's context (it also requires a hypothesis `∀ g, _ ≤ Φ.mass g`), as for
(G-ex₂) and (X₁), since a plain `by assumption` picks `0 < P.Λ` (the build failed that way).
Each binder's type is exactly the frozen one. (Earlier notes said the default "fixes `m₀` from
`hmass`"; the 2026-11-21 audit showed it resolves `m₀` by name, failing loudly if renamed.)

Checks: the frozen bytes changed only in the four proof bodies; the module and provider builds
exit 0 with no warnings in these eight modules; standard axioms only (4/4 anchors and 4/4
providers); ABI unchanged (4/4, recomputed for these exports with the `frozen_abi.py` method;
the full `frozen_abi.py --check` passes); after erasing `autoParam` and binder information,
each provider type is `Expr.eqv` to the frozen type (4/4); guard OK.
Independent seal audit (refute-first, 2026-11-21): all four PROVED, APPROVE-WITH-FIXES (wording
only: the binder note above). It checked the frozen diff, type equality and that each frozen
hypothesis reaches its own slot (`pp.explicit`), standard axioms, transitive quarantine, that
the three share inputs are proved for every `D` (so `hD` is genuinely unneeded: the share and
its Ward identity hold for any counterterm values; `hD` matters only for (HS₆)), and
non-vacuity of `IsSetA`, `IsVPChain 2` and (Sc₃) at order 7.

**Seal of (E-G₄) (2026-11-22).** The D-58 goal (E-G₄) `QED.Graded.familyVertex_isVPChain_two`
is sealed with the provider `QED.Provider.Graded.familyVertex_isVPChain_two` ←
`QED.ChainProof.EG4.familyVertex_isVPChain_two'` (`QED/ChainProof/EG4Bridge.lean`). A
two-insertion chain has only `gauge` and `photonCt` vertices and total order `7`, so at graded
order `7` only the zero grading contributes (`grading_eq_zero_of_isVPChain`); the graded sum and
the chain sum then agree term by term (`GradedProof.contractionValue_zero_eq`), the level-`0`
photon-counterterm factor `e² d₃ 0` being `δ₃` by `h₃`. No representatives or relabelling are
needed. 13 of the 17 D-58 goals are sealed; the statements stay provisional with the rest of
D-58.

Checks: the frozen bytes changed only in the proof body and the manifest state; the frozen and
provider builds exit 0 with no warnings; standard axioms (anchor and provider); guard OK; the
full `frozen_abi.py --check` passes. Independent seal audit (refute-first, 2026-11-22): PROVED.
It checked the frozen diff, type equality up to D-13 binders with each argument (including `h₃`)
in its own slot, standard axioms, the transitive quarantine, that `grading_eq_zero_of_isVPChain`
holds for every grading, that both sides agree term by term with no sum set to zero by fiat,
that `vertexChain 2` is non-trivial (HC₃ consumes it), and that `h₃` is what matches the
`photonCt` terms. Ledger wording was corrected: (E-G₄) is one bridge toward a graded-model
statement of the set (b) headline, not that statement itself.

**Seal of (R-Π₄) (2026-11-22). Stage 2 complete.** The last Stage 2 goal (D-57, approved by the
author), `QED.Graded.vacuumPolarizationPart_two_lepton_limit`, is sealed with the provider
`QED.Provider.Graded.vacuumPolarizationPart_two_lepton_limit`. The provider applies the assembly
`QED.GradedProof.RPi4.vacuumPolarizationPart_two_lepton_limit_of_incPieces`
(`QED/GradedProof/RPi4Wire2Asm.lean`) to the per-piece A-increment bounds
(`faceRateIncAQ_piecesAB_incPieces`, `RPi4FaceRateIncAClass.lean`) and B-increment bounds
(`faceRateIncBPiecesAB_incPieces`, `RPi4FaceRateIncW11.lean`). The assembly consumes the
heavy-density ray input (`wire2_wireDRay`), the face-rate majorant
(`faceIdRayAQ_majFaceRate_cfg4`, `wire2_majFaceRate`), the fixed-density input
(`wire_fixDens_of_gen`, from `wire2_wireDRayGen` and `wire2_wireFaceRateGen`) and the
scale-Lipschitz input `MajLimLip4` (`wire2_limLip4_of_pieces`), all
proved. The Hölder shortcut was ruled out: the frozen majorant clause covers regulator masses
arbitrarily close together, which forces the full Lipschitz factor. All 18 Stage 2 goals are now
sealed.

Checks: the frozen bytes changed only in the proof body and the manifest state; the frozen and
provider builds exit 0; standard axioms; guard OK; the full `frozen_abi.py --check` passes.
Independent seal audit (refute-first, 2026-11-22): PROVED. It checked the frozen diff, type
equality up to D-13 binders with every argument in its own slot, standard axioms for the anchor,
the provider and the ten theorems of the assembly chain (no axiom, sorry, native_decide,
implemented_by or extern anywhere in the 876-module closure), the quarantine, that every
conditional premise along `_of_incPieces` → `_of_limLip4` → `_of_gen` → `_of_dens` is
discharged by a proved term, and non-vacuity (the renormalized counterterms exist by
`exists_renormalized`; `Π_∞` is a genuine witness). The identification of `Π_∞` with the
Källén–Sabry function is not part of R-Π₄; it is the set (a) step R-KS (deferred item D6).

**Seal of (HA₀) (2026-11-22; provisional freeze, author approval pending).** The D-58 goal
`QED.ThreeLoop.jointEnergyFirstIntegrable_setA` is sealed with the provider
`QED.Provider.ThreeLoop.jointEnergyFirstIntegrable_setA` (D-13 binders), which applies
`QED.ChainProof.SetALink.jointEnergyFirstIntegrable_setA_final` (`SetALinkIntFinal.lean`). That
theorem discharges the class obligations of the nine representatives of
`jointEnergyFirstIntegrable_setA_of_classes`:
the one-loop photon-counterterm classes (`classIntA_repP`, X₀'s one-loop test), the two-loop
gauge-counterterm classes (`classIntA_repGW`, `classIntA_repGU`), the two-loop
fermion-counterterm classes (`classIntA_repFA`, `classIntA_repFB`, after the rewrite
k̸k̸ = −k·k at the counterterm vertex) and the three-loop vertex-type classes
(`classIntA_repVA`, `classIntA_repVB`, `classIntA_repVC`, by a three-loop lines theorem from
rotating the three loop energies under a kernel-checked basis criterion).
Checks: the frozen bytes changed only in the proof body and the manifest state; the frozen and
provider builds exit 0; standard axioms; guard OK; full `frozen_abi.py --check` passes.
Independent seal audit (refute-first, 2026-11-22): PROVED. It checked the frozen diff, type
equality with every argument in its own slot, standard axioms across the 56,817-constant closure
(no sorryAx, unsafe or QED-namespace extern), the quarantine, that the classification
`exists_rep_setA` covers every set (a) contraction at graded order 7 by the nine
representatives, that the kernel-checked criteria are hypotheses actually consumed, and that the
class hypotheses are exactly the frozen statement's.

**Seal of (HS₀) (2026-11-22; provisional freeze, author approval pending).** The D-58 goal
`QED.ThreeLoop.jointEnergyFirstIntegrable_setC` is sealed with the provider
`QED.Provider.ThreeLoop.jointEnergyFirstIntegrable_setC` (D-13 binders), which applies
`QED.ChainProof.SetCLink.jointEnergyFirstIntegrable_setC_final` (`SetCLinkIntD.lean`). That
theorem discharges, through `jointEnergyFirstIntegrable_setC_of_remaining` and `RemainingC.ofB`,
the class obligations of the set (c) classification `exists_rep_setC`: the B family (two-loop
graphs with the bubble on a photon line), the D family (24 orbits with the δ₃ element, the
`k·k g` part directly and the `k_μ k_ν` part by internal or one-sided external Ward identities,
each criterion checked by `decide +kernel`), the counterterm classes CB0, CB1 and the degree-6
classes CD0, CD1, with the remaining classes proved earlier.
Checks: the frozen bytes changed only in the proof body and the manifest state; the frozen and
provider builds exit 0; standard axioms; guard OK; full `frozen_abi.py --check` passes.
Independent seal audit (refute-first, 2026-11-22): PROVED. It checked the frozen diff (proof
body and manifest state only; prefix and suffix hashes recomputed), the elaborated provider type
equal to the frozen one, the ABI fingerprint `775dc748…` reproduced, every class obligation of
`RemainingC.ofB` and `classesC_of_remaining` discharged by a proved theorem, standard axioms
with a forbidden-token scan of the 392-module closure, the quarantine, and that every
meaning-carrying definition in the statement is a sealed frozen definition.

## D-59. Rulings of 2026-11-22: set (a) approved, set (d) packet frozen (author ruling)

**Rulings.** On 2026-11-22 the author ruled as follows.

1. **Set (a) statements approved.** The ten set (a) entries frozen provisionally under D-58 move
   from approval version "provisional" to "1", with this decision as their approval reference:
   (A₁) `IsSetA`, (A₂) `a1SixSetA`, (A₃) `a1SixSetA_bounds`, block K ((A₄) `ksRhoFour`, (A₅)
   `piHatFour`, (A₇) `integral_piHatFour_eq_a1SixSetA`), the meaning theorems (MA₁)
   `exists_isSetA` and (MA₂) `not_isSetA_and_isVPChain_two`, (HA₀)
   `jointEnergyFirstIntegrable_setA` and the headline (HA₆)
   `isFormFactorPair_vertexSetA_pauli_limit` (state SEALED). Only the `author_approval` fields
   changed; the frozen bytes, hashes, states and split policies are unchanged. The set (c) entries
   and the generic `QED.Graded` entries of D-58 ((Gf₁), (Gf₂), (Gs₁)–(Gs₃), (MF₁), (MS₁), (MS₂),
   (E-G₄)) were not part of this approval and stay provisional. With (HA₆) sealed (commit
   `68c967b`), milestone L3.SETA is done.
2. **Set (d) packet frozen as audited.** The Stage 3d packet (session scratch,
   `packetD/Packet/SetD.lean`) is frozen with the author's approval, one declaration per file
   under `QED/Frozen/ThreeLoop/`, namespace `QED.ThreeLoop`:
   - definitions (SEALED, bodies exposed, imported by `QED.lean`): (Sd₁) `IsSetD`, the one-loop
     vertex skeleton whose external photon sits on a four-photon fermion loop joined to the open
     line by three photons (AKN Fig. 3 (d), six diagrams, no counterterm graph); (Sd₂)
     `a1SixSetD`, the Laporta–Remiddi (1991) closed form as printed by Jegerlehner–Nyffeler,
     p. 32, ≈ 0.3710052921072;
   - theorem goals (DRAFT_SORRY, body `by sorry`): (Sd₃) `a1SixSetD_bounds`, (MD₁)
     `exists_isSetD`, (MD₂) `isSetD_disjoint`, (HD₀) `jointEnergyFirstIntegrable_setD` and the
     headline (HD₆) `isFormFactorPair_vertexSetD_pauli_limit`, which has the binders and
     quantifier order of (HA₆) with selection `IsOnePI ∧ IsSetD` and target `a1SixSetD`. Each
     names a provider under `QED.Provider.ThreeLoop` in the D-13 convention; as for D-58, the
     provider modules are quarantined stubs (imports and a docstring only, no declaration),
     imported only by their frozen anchors. The root does not import the theorem anchors.

   The frozen text is byte-identical to the audited candidate except for two docstring changes in
   (Sd₂), both ruled by the author: the Laporta–Remiddi 1991 page is 181, as the reference list of
   Laporta–Remiddi 1996 prints it (the draft had 182), and Jegerlehner–Nyffeler is cited as the
   pinned source `jegerlehner-nyffeler-2009`. The redundant hypothesis `hC₁ : IsOnePI C` of
   (HD₀) is kept (audit question Q-d4), for uniformity with (HS₀); the enumeration shows every
   (Sd₁) contraction at order 7 is 1PI. The manifest entries (contract prefix
   `qed_dev.packetS3d`) were computed with the D-58 freezer, whose only change is that it accepts
   the candidate's `:=` / `sorry` body form. The ABI hashes come from the `frozen_abi.py`
   method, and the definition closures from the D-58 closure walk.

   Audit (independent, refute-first, 2026-11-22; session scratch `packetD/AUDIT.md`): all seven
   PASS, no FAIL. The audit enumerated all 4,233,600 seven-gauge contractions. (Sd₁) selects
   6 · 7! of them: six orbits without automorphisms, all 1PI, with no extra or missing graph.
   (Sd₂) was checked term by term against the rendered page and to 40 digits. (Sd₃) and (MD₁)
   are proved in scratch with standard axioms only. (MD₂) is true at every order and grading.
   (HD₀) differs from the sealed (HS₀) only in the selection. (HD₆) was shown by elaboration to
   be the (HA₆) shape with the selection and target replaced.
3. **Source pinned.** F. Jegerlehner and A. Nyffeler, *Phys. Rept.* 477 (2009) 1,
   arXiv:0902.3360v1, is pinned as `jegerlehner-nyffeler-2009` (2592813 bytes, sha256
   `285594c721d849dc525523a41f07de1c1aefff0f0887744eec465ca8aeb70651`) in `sources/manifest.json`
   and [SOURCES.md](../SOURCES.md), where it was a background reference. On 2026-11-22 the hash
   was re-verified against the session's downloaded copy, which is the hash recorded on
   2026-11-07. That copy is now also in the ignored `sources/cache/`.
4. **Model-link pilot.** The model-link pilot continues as planned: the generic layers first, then
   the X graph, then L and S+C. The pilot is re-sized after X.

**Still drafts.** Set (e) and the total (the value split and the assembly of A₁⁽⁶⁾) remain drafts
and are not frozen. Before the total's value-split statement (CMP₇-v)
`familyVertex_seven_eq_sum` is frozen, the auditor recommends adding `hε : 0 < P.ε`. Without
it, `contractionValue`'s junk value 0 at a non-integrable stage can break additivity in the
level-1 data. The auditor also suggests considering the (X₀) block and stating `hs` at
`Φ.openLine` only.

## D-60. Rulings of 2026-11-22: trace scheme and graded vertex definitions (author ruling)

1. **Dirac-trace scheme of the model link: accepted.** The `d`-dimensional Dirac algebra of
   projected numerators in the model ↔ dimensional-regularization bridge is the conventional
   one: `{γ^μ, γ^ν} = 2 g^{μν}`, `g^μ_μ = d`, `tr 1 = 4`, no `γ₅`. It is a choice of scheme,
   not a consequence of the four-dimensional model. Every projected numerator is a named,
   exposed definition in `QED/DimReg/TwoLoopBridgeTrace*.lean`, with a proved theorem that it
   equals the model's four-dimensional trace numerator at `d = 4`. The first entry is the
   one-loop `QED.DimReg.OneLoopBridge.pauliNum` (commit 045272f). New entries follow the same
   form and are reviewed by the orchestrator as they land.
2. **`QED.Graded.familyVertex` and `QED.Graded.IsFamilyVertexLimit`: approved.** The author's
   set (a) approval (D-59) extends to these two definitions, frozen provisionally under D-58,
   on which the set (a) headline depends (they are also used by the set (c) and (d)
   headlines). Their manifest entries `graded.family_vertex_v1` and
   `graded.is_family_vertex_limit_v1` change only in `author_approval`. The meaning theorems
   `familyVertex_isOnePI` and `familyVertex_isVPChain_two` and the set (c) packet stay
   provisional.
3. **`d`-dimensional Pauli projector: accepted.** Contracted in `d` dimensions, the model's
   four-dimensional Pauli projector `pauliMat` leaks `F₁` at order `d - 4` (its trace against
   `γ^μ` is `2m q²(q² + 4m²)(d - 4)`), which would add a spurious finite term wherever it
   multiplies a pole. The bridge uses instead
   `P^d = A_d N(p) γ_μ N(p') + B_d (p + p')_μ N(p) N(p')` with
   `A_d = 2m(4m² + Q)/(d - 2)` and `B_d = Q - 4m²/(d - 2)`
   (`QED.DimReg.TwoLoopBridgeTraceX.pauliProjA`, `pauliProjB`): the unique coefficients that
   annihilate `F₁` exactly and keep the `F₂` normalization independent of `d`, equal to the
   model's projector at `d = 4` (`pauliMat_eq_pauliProj`, `pauliProj_annihilates_F₁`,
   `pauliProj_normalization`). It reproduces the one-loop `pauliNum` exactly. The crossed-graph
   numerators `psiT1d`, `psiT2d` are defined with it and checked against the model's `psiT1h`,
   `psiT2h` at `d = 4`.
