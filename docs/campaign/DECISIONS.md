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
