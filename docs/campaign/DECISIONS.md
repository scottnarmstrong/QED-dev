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
