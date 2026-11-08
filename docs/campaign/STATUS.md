# Campaign status

[Campaign HQ](../../README.md) · [Decisions](DECISIONS.md) · [Findings](FINDINGS.md) ·
[Progress ledger](progress.json)

**As of 2026-11-08.** Phase 1 (fix the one-loop calculation), preparation stage.

Milestones (see the [ledger](progress.json)):

| Milestone | Status |
| --- | --- |
| SPEC.SOURCE, SPEC.ROUTE, SPEC.ENV | done, on the evidence below |
| SPEC.STATEMENTS | in progress: packet 1 approved and frozen (D-11); packets 1b and 2 pending |
| L1.MODEL | in progress: algebra infrastructure only |
| L1.PROJECTION | in progress: spinors, normalization, and the Gordon identity |
| L1.INTEGRAL | in progress: energy integrals (O-7) only |

## Reporting fields

```text
DRAFT_ANCHORS: 1 — QED/Frozen/OneLoop/VertexLimitExists.lean (QED.OneLoop.vertexLimit_existsUnique;
               provider QED.Provider.OneLoop.VertexLimitExists, empty so far)
UNREGISTERED_SORRIES: 0 (scripts/check_frozen_anchors.py: FROZEN-ANCHOR GUARD OK)
DRAFT_IMPORT_VIOLATIONS: 0 (same guard run)
SEALED_THIS_TURN: 0 theorems. Packet 1 definitions (A)–(D) were frozen as SEALED
               definition anchors; they are definitions, not proofs.
```

| Field | Value |
| --- | --- |
| Model / prescription | Perturbative QED in Feynman gauge with the on-shell scheme, starting from a momentum-space Wick expansion at order $e^3$ (D-8). The one-loop pilot uses a Pauli–Villars photon (mass $\Lambda$) and a photon mass $m_\gamma$, with Minkowski loop integrals defined by the energy-first prescription M1 ([REGULARIZATION.md](../REGULARIZATION.md); D-5). The magnetic moment has two definitions, the source's wave-packet definition and the vertex response, proved equivalent (D-9). |
| Base commit for this work | `67a0e50`. The landing commits follow it on `main`. |
| Retained external inputs | none. No conditional results exist. |
| Pending author decisions | **Packet 1b**: approval of the exact bodies of `QED.Minkowski.metric`, `dot`, `lower`, `QED.Dirac.gamma`, and `slash`, to freeze packet 1's closure ([F-12](FINDINGS.md)). Earlier rulings: D-8, D-9, D-10, and D-11 (packet 1 approved and frozen, 2026-11-08). |

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
  - `QED/Algebra/Contraction.lean`: `gammaLower`, the anticommutators
    $\{\gamma_\mu,\not a\}=-2a_\mu$ and $\{\not a,\not b\}=-2(a\cdot b)$, the
    recursion `contract_mul_slash`, and the contraction identities (47.18)–(47.21)
    at $d=4$. These are the identities obligation O-4 uses.
  - `QED/Algebra/Spinor.lean`: the Dirac adjoint `bar` (38.7), the rest spinors
    (38.6), the closed-form spinors $u_s(p)=(m-\not p)u_s(0)/\sqrt{2m(m+p^0)}$, the
    Dirac equations (38.1) and (38.16), the normalization
    $\bar u_{s'}(p)u_s(p)=2m\delta_{s's}$ (38.17), and `gordon_spinor`.
  - `QED/Integration/EnergyIntegral.lean` (milestone L1.INTEGRAL, in progress):
    obligation O-7, the loop-energy integrals with Wick rotation replaced by
    analytic continuation.
    - Real integrals: $\int(1+t^2)^{-2}=\pi/2$ and $\int(1+t^2)^{-3}=3\pi/8$.
    - A locally uniform lower bound near the slit plane.
    - The continuation principle `integral_sq_add_zpow_of_real`.
    - On the slit plane: $\int(t^2+z)^{-2}=\frac{\pi}{2}z^{-3/2}$,
      $\int(t^2+z)^{-3}=\frac{3\pi}{8}z^{-5/2}$, and
      $\int t^2(t^2+z)^{-3}=\frac{\pi}{8}z^{-3/2}$.
    - The mostly-plus forms $\int(-t^2+w)^{-3}=-\frac{3\pi}{8}(-w)^{-5/2}$ and
      $\int t^2(-t^2+w)^{-3}=-\frac{\pi}{8}(-w)^{-3/2}$.
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
| Project build | `nice -n 5 lake build` | success; 2901 jobs, no warnings |
| Module system | `check_lean_modules.py --root .` (lean-project-architecture skill) | PASS (8 Lean files) |
| Axioms | `#print axioms` on all 58 theorems and lemmas in `QED/` (transient file, deleted) | only `propext`, `Classical.choice`, `Quot.sound` |
| Forbidden tokens | grep for `sorry`, `admit`, `axiom`, `maxHeartbeats`, `native_decide` over `QED/` and `QED.lean` | one `sorry`: the registered `DRAFT_SORRY` body of (E), authorized by the manifest; nothing else |
| Source bytes | `python3 scripts/fetch_sources.py` | 5/5 OK |
| Numerical sanity (not proofs) | `python3 scripts/numerics/one_loop_sanity.py` | all eight checks pass |
| HQ consistency (not a proof check) | `python3 scripts/update_hq.py --check` | run at each landing |
| Frozen-anchor guard | `python3 scripts/check_frozen_anchors.py --root . --manifest QED/Frozen/manifest.json` | `FROZEN-ANCHOR GUARD OK`; rejected all five negative tests (statement edit, body edit, unregistered `sorry`, draft import, provider import) |
| Frozen ABI hashes | `python3 scripts/frozen_abi.py --check` | 5/5 OK |
| Independent document review | refute-first reviewer (not the writer). It checked SOURCES, CONVENTIONS, REGULARIZATION, and ONE-LOOP-DERIVATION against the pinned PDFs: about 45 Srednicki citations, the dictionary and conventions numerically, and the integrals, bounds, and limits | No wrong source citation and no sign or normalization error in the load-bearing chain. 16 findings, all addressed before landing: 3 errors (an asymptotic stated for $n=1$; the remainder term of the photon-mass deficit; leg corrections listed as parts of the 1PI $V^\mu$), 5 weak claims, 8 nits |

A documentation check is not a Lean build. A floating-point check is not a
proof.

## Remaining obligations and next bounded tasks

1. **Carriers.**
   - Equality of the closed-form spinors with the source's boost definition
     (38.12). This is needed before the source definition of the magnetic
     moment, which uses (64.11)–(64.12).
   - On-shell momenta as a carrier, and the on-shell sandwich structure:
     independence of the bilinears $\bar u'\gamma^\mu u$ and
     $\bar u'S^{\mu\nu}q_\nu u$ for $q\neq0$, the uniqueness half of O-15.
   - The energy-first Minkowski loop integral (prescription M1), with explicit
     integrability, so that no definition depends on Lean's zero value for
     non-integrable integrands.
2. **Infrastructure the rulings add.**
   - Wick contractions with fermionic signs for the order-$e^3$ expansion (D-8).
   - One-particle states, wave packets, and one-particle current matrix
     elements for the source definition of the magnetic moment (D-9).
3. **Packet 1 follow-ups.** Obtain approval of packet 1b ([F-12](FINDINGS.md)).
   Prove (E) in the provider `QED.Provider.OneLoop.VertexLimitExists`, then seal
   and audit it.
4. **Exact declarations.** Prepare packet 2 as planned in
   [ONE-LOOP-DERIVATION.md](../ONE-LOOP-DERIVATION.md#proposed-anchor-surface-for-the-first-review-packets):
   the form-factor decomposition (O-15) and the headline, as transient,
   elaborated commands. They depend on the one-loop vertex of step 1e, which can
   be defined only after (E) is proved. Obtain an independent
   source/binder review, then bring the author a review packet. Nothing is
   frozen before approval.

No exact declaration is ready for approval: the carriers above do not exist yet.
