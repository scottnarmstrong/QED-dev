# Campaign status

[Campaign HQ](../../README.md) · [Decisions](DECISIONS.md) · [Findings](FINDINGS.md) ·
[Progress ledger](progress.json)

**As of 2026-11-07.** Phase 1 (fix the one-loop calculation), preparation stage.

Milestones (see the [ledger](progress.json)):

| Milestone | Status |
| --- | --- |
| SPEC.SOURCE, SPEC.ROUTE, SPEC.ENV | done, on the evidence below |
| SPEC.STATEMENTS | planned: no exact declaration exists yet |
| L1.MODEL | in progress: algebra infrastructure only |
| L1.PROJECTION | in progress: Gordon identity only |

## Reporting fields

```text
DRAFT_ANCHORS: 0 / none after inspection (no frozen files, no manifest)
UNREGISTERED_SORRIES: 0 / none after inspection (grep for sorry/admit over QED/ and QED.lean)
DRAFT_IMPORT_VIOLATIONS: 0 / none (no draft anchors exist)
SEALED_THIS_TURN: 0
```

| Field | Value |
| --- | --- |
| Model / prescription | Perturbative QED in Feynman gauge with the on-shell scheme, starting from a momentum-space Wick expansion at order $e^3$ (D-8). The one-loop pilot uses a Pauli–Villars photon (mass $\Lambda$) and a photon mass $m_\gamma$, with Minkowski loop integrals defined by the energy-first prescription M1 ([REGULARIZATION.md](../REGULARIZATION.md); D-5). The magnetic moment has two definitions, the source's wave-packet definition and the vertex response, proved equivalent (D-9). |
| Base commit for this work | `67a0e50`. The landing commits follow it on `main`. |
| Retained external inputs | none. No conditional results exist. |
| Pending author decisions | none. Rulings received on 2026-11-07: D-8 (model starting point), D-9 (both magnetic-moment definitions, proved equivalent), D-10 (Apache-2.0); see [DECISIONS.md](DECISIONS.md). |

## Work completed

- **Sources** ([SOURCES.md](../SOURCES.md), D-6).
  - Primary source: the Srednicki draft, chapters 58 and 62–64. Secondary
    source: the Kaplunovsky vertex notes. Three background sources.
  - All are pinned by SHA-256 in
    [`sources/manifest.json`](../../sources/manifest.json), with the bytes in an
    untracked cache (D-2).
  - Every chain item from the Lagrangian to $g=2(1+\alpha/2\pi)$ is mapped to
    pages and equations.
- **Conventions** ([CONVENTIONS.md](../CONVENTIONS.md), D-7). The source's
  conventions, with a dictionary to the mostly-minus convention.
- **Route** ([REGULARIZATION.md](../REGULARIZATION.md), D-5).
  - Three regulator routes compared, with a reasoned choice for the pilot.
  - A definition of the Minkowski loop integral, needed because Feynman-$i\epsilon$
    integrals are not Lebesgue integrals (F-1).
  - Renormalization conditions, gauge, order of limits, positivity bounds, and
    the explicit regulator dependence of the target.
- **Derivation** ([ONE-LOOP-DERIVATION.md](../ONE-LOOP-DERIVATION.md)).
  - Stages 0–5, from model data to the magnetic interpretation, with
    obligations O-1 to O-23.
  - The carriers needed for the exact declarations, and why the form factors
    need an existence-and-uniqueness theorem first.
- **Findings** ([FINDINGS.md](FINDINGS.md)).
  - F-1: the Minkowski integral is not absolutely convergent.
  - F-2: the regulator deviates from the source's.
  - F-3 to F-6: four source misprints, verified against the pinned bytes and
    the author's errata.
  - F-7 and F-8: source gaps.
  - F-9: secondary-source misprints.
  - F-10: a candidate issue in a background source.
- **Mathlib inventory** ([MATHLIB-INVENTORY.md](../MATHLIB-INVENTORY.md)).
  61 topics: 44 available, 8 partial, 9 missing. The worker verified the names
  by grep; 26 sampled names were then elaborated in Lean.
- **Lean environment** (D-3, D-4). Lean `v4.35.0` and Mathlib `v4.35.0`
  (`56a00585…`), package `qed`, library `QED` built with `.andSubmodules`.
- **First proved infrastructure** (milestone L1.MODEL is in progress; this is
  not a source-facing result):
  - `QED/Algebra/Minkowski.lean`: the mostly-plus metric, `dot`, `lower`, and
    `metric_mul_metric`.
  - `QED/Algebra/Dirac.lean`: the Weyl gamma matrices of (36.7), the Clifford
    relation `gamma_anticomm` (36.9), `β` (38.8) with
    `beta_mul_conjTranspose_gamma_mul_beta`, `slash` with `slash_mul_slash`,
    and `lorentzGen` (40.3).
  - `QED/Algebra/Gordon.lean` (milestone L1.PROJECTION, in progress):
    `gamma_mul_gamma` ($\gamma^\mu\gamma^\nu=-g^{\mu\nu}-2iS^{\mu\nu}$),
    `gamma_mul_slash` (38.19), `slash_mul_gamma` (38.20), and the Gordon
    identity `gordon` (38.18). The identity is stated for any column vector $u$
    with $(\not p+m)u=0$ and any row vector $w$ with $w(\not p'+m)=0$ (obligation
    O-14).
- **Administration** (D-1, D-10). The repository was made public at the
  author's instruction, and `jaumededios` was invited with write access. It is
  now licensed under Apache-2.0: `LICENSE`, plus the header line in every Lean
  file.
- **Author rulings recorded** (D-8, D-9). The model starts from a
  momentum-space Wick expansion. Both magnetic-moment definitions will be
  formalized and proved equivalent. The derivation's stages 0 and 5 and its
  carrier table are updated, and obligation O-24 (equivalence) is added.

## Validation

| Check | Command | Result |
| --- | --- | --- |
| Baseline environment | `lake build --no-build` after copying the dependency tree | Mathlib and its dependencies up to date; no rebuild |
| Transient import probe | `lake env lean` on an untracked module importing the focused sets (file deleted) | 26/26 sampled inventory names elaborate; all loaded from cache in under 5 s |
| Project build | `nice -n 5 lake build` | success; 1321 jobs |
| Module system | `check_lean_modules.py --root .` (lean-project-architecture skill) | PASS (5 Lean files) |
| Axioms | `#print axioms` on all 16 theorems in `QED/Algebra/` (transient file, deleted) | only `propext`, `Classical.choice`, `Quot.sound` |
| Forbidden tokens | grep for `sorry`, `admit`, `axiom`, `maxHeartbeats`, `native_decide` over `QED/` and `QED.lean` | none |
| Source bytes | `python3 scripts/fetch_sources.py` | 5/5 OK |
| Numerical sanity (not proofs) | `python3 scripts/numerics/one_loop_sanity.py` | all eight checks pass |
| HQ consistency (not a proof check) | `python3 scripts/update_hq.py --check` | run at each landing |
| Independent document review | refute-first reviewer (not the writer). It checked SOURCES, CONVENTIONS, REGULARIZATION, and ONE-LOOP-DERIVATION against the pinned PDFs: about 45 Srednicki citations, the dictionary and conventions numerically, and the integrals, bounds, and limits | No wrong source citation and no sign or normalization error in the load-bearing chain. 16 findings, all addressed before landing: 3 errors (an asymptotic stated for $n=1$; the remainder term of the photon-mass deficit; leg corrections listed as parts of the 1PI $V^\mu$), 5 weak claims, 8 nits |

A documentation check is not a Lean build. A floating-point check is not a
proof.

## Remaining obligations and next bounded tasks

1. **Carriers.**
   - Explicit on-shell spinors (38.6), (38.12), their normalization (38.17),
     and the Dirac equation for $\bar u$ (38.16) from that for $u$. The
     Gordon identity itself is proved.
   - The contraction identities (47.18)–(47.21) needed by O-4.
   - The energy-first Minkowski loop integral (prescription M1), with explicit
     integrability, so that no definition depends on Lean's zero value for
     non-integrable integrands.
   - The energy-integral continuation lemma O-7.
2. **Infrastructure the rulings add.**
   - Wick contractions with fermionic signs for the order-$e^3$ expansion (D-8).
   - One-particle states, wave packets, and one-particle current matrix
     elements for the source definition of the magnetic moment (D-9).
3. **Exact declarations.** Once the carriers exist, prepare the regulated
   one-loop vertex (62.40) and the existence-and-uniqueness theorem for the form
   factors (O-15) as transient, elaborated commands. Obtain an independent
   source/binder review, then bring the author a review packet. Nothing is
   frozen before approval.

No exact declaration is ready for approval: the carriers above do not exist yet.
