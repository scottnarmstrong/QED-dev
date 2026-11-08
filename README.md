# QED-dev — campaign HQ

**Verified calculations in quantum electrodynamics, aimed at predictions that can
be compared with experiment.** We are building a Lean 4 + Mathlib development
around the electron's anomalous magnetic moment, $a_e=(g_e-2)/2$: from the QED
rules, through renormalized amplitudes, to certified numerical results and an
explicit uncertainty budget.

The first scientific milestone is the **complete one-loop Schwinger calculation**,
$a_e^{(1)}=\alpha/(2\pi)$. The longer route runs through two loops and selected
higher-loop contributions toward a verified five-loop QED prediction. Each stage
should produce reusable tools for real physics calculations.

**Current state (Phase 1, preparation):** the primary derivation is pinned
(Srednicki, chapters 62–64). The conventions are fixed, and the one-loop
regulator route is chosen. The derivation is mapped step by step with its proof
obligations exposed. A Lean package is pinned to Lean and Mathlib `v4.35.0`.
It contains proved Dirac-algebra infrastructure, the loop-energy integral
evaluation that replaces Wick rotation, and the **first author-approved frozen
declarations** (packets 1 and 1b, D-11 and D-12): the regulated propagators,
the one-loop vertex integrand (62.40), the energy-first integral, the Minkowski
and Dirac definitions they are built from, and the theorem goal that the
regulated vertex is well defined. **That theorem is now proved** (sealed and
independently audited). It establishes that the regulated one-loop vertex
exists; the value of $F_2$ is not yet proved. See the
[campaign status](docs/campaign/STATUS.md).

**Start here:** [What does "proved" mean?](docs/WHAT-IS-PROVED.md) ·
[Project outline](docs/PROJECT-OUTLINE.md) ·
[Orchestrator launch](docs/ORCHESTRATOR-LAUNCH.md) ·
[Campaign status](docs/campaign/STATUS.md) · [Immediate next steps](#next-steps) ·
[Progress data](docs/campaign/progress.json) · [Working rules](AGENTS.md)

## Progress

The meters count completed, explicitly listed milestones. They measure neither
effort nor experimental precision, and they are not an estimate of how much of
QED has been formalized. Campaign setup is kept separate from mathematical work.
The longer-term milestone lists will be refined as their sources and statements
become precise; changes to their scope must be recorded.

<!-- HQ:progress:start -->
**Ledger updated:** 2026-11-08. Only milestones marked `done` contribute to the meters.

| Workstream | Complete | Milestone meter | State |
| --- | ---: | --- | --- |
| Campaign setup | 4/4 | `██████████` 100% | Complete |
| Sources and exact specification | 3/4 | `███████░░░` 75% | In progress |
| Complete one-loop calculation | 0/8 | `░░░░░░░░░░` 0% | In progress |
| Numerical certification pilot | 0/4 | `░░░░░░░░░░` 0% | Planned |
| Complete two-loop calculation | 0/4 | `░░░░░░░░░░` 0% | Planned |
| Higher loops toward five-loop QED | 0/4 | `░░░░░░░░░░` 0% | Planned |
| Experimental comparison | 0/4 | `░░░░░░░░░░` 0% | Planned |

**Tracked Lean source files:** 42. Documentation milestones do not count as proved physics.
<!-- HQ:progress:end -->

The [progress ledger](docs/campaign/progress.json) is the source of these meters.
Update an item's status and evidence, then run:

```bash
python3 scripts/update_hq.py
python3 scripts/update_hq.py --check
```

`--check` checks ledger consistency, evidence paths, and synchronization with HQ;
it does not verify Lean proofs. Formal milestones need Lean evidence and a
validation record before they may be marked complete. No scheduled updater is
installed.

## What the campaign must connect

| Part | Deliverable |
| --- | --- |
| Sources and specification | A fixed calculation, conventions, and exact source-facing Lean declarations |
| QED algebra and amplitudes | Verified diagram generation, fermionic signs, Dirac algebra, and amplitude transformations |
| Renormalization and analysis | A precise prescription, justified subtractions and integral manipulations, and regulator limits |
| Magnetic observable | The connection between the vertex form factor $F_2(0)$ and the magnetic moment |
| Numerical certification | Checkable certificates for integral enclosures, including rounding and integration errors |
| Experimental comparison | Sourced inputs, propagated uncertainties, and explicit treatment of omitted contributions |

These are parts of one calculation. The one-loop result counts only when the
chain from the defined perturbative QED model to the magnetic observable is
proved. Checking an integral supplied at the end of a derivation is useful, but
does not complete that chain.

## Scientific targets

1. **One loop:** derive the magnetic form factor and prove its first QED
   coefficient, including the connection to the measured observable.
2. **Two loops:** certify the complete contribution, including counterterms and
   cancellations, using infrastructure that extends beyond the one-loop case.
3. **Higher loops:** certify a selected published family, then expand toward the
   full five-loop QED contribution, including lepton-mass dependence.
4. **Prediction:** assemble certified coefficient bounds with independent physical
   inputs and the required non-QED contributions to support an experimental test.

The [outline](docs/PROJECT-OUTLINE.md) gives the scope, stages, proposed module
areas, completion criteria, and initial sources. These are planning targets;
none is an approved or frozen Lean declaration yet.

## What a result certifies

The reader-facing guide [What does it mean to prove a QED calculation?](docs/WHAT-IS-PROVED.md)
explains the model, computational rules, and the meaning of each kind of claim.

We distinguish exact perturbative coefficients, certified numerical enclosures,
analytic bounds for omitted terms, and comparison with experimental data.
Agreement at a finite perturbative order does not supply a remainder bound.
Statistical error bars are recorded with their statistical assumptions; they are
not presented as deterministic enclosures.

Physical postulates and deliberately retained external inputs must be visible.
Proof steps must be proved rather than placed inside a model assumption.
Completed formal results require source review, a build at the recorded revision,
and an axiom audit. Empirical accuracy is always attached to a specified
observable, input dataset, and uncertainty budget.

## Next steps

Done in Phase 1 so far: [sources](docs/SOURCES.md), [conventions](docs/CONVENTIONS.md),
[regulator route](docs/REGULARIZATION.md), [derivation and obligations](docs/ONE-LOOP-DERIVATION.md),
the [Mathlib inventory](docs/MATHLIB-INVENTORY.md), the pinned Lean package, and
the first algebra infrastructure.

1. Continue building the missing carriers as proved infrastructure: the
   definition of the energy-first Minkowski loop integral, on-shell momenta and
   the uniqueness of the form-factor decomposition, and the boost form of the
   spinors. The energy-integral evaluation (O-7) is done. The Dirac
   algebra is done: Clifford relation, contraction identities, spinors with
   normalization, and the Gordon identity.
2. Build the infrastructure the author's rulings require: Wick contractions
   with fermionic signs for the order-$e^3$ expansion (D-8), and one-particle
   states, wave packets, and current matrix elements for the source definition
   of the magnetic moment (D-9).
3. Prepare the exact source-facing declarations, starting with the regulated
   one-loop vertex and the existence-and-uniqueness theorem for the form
   factors. Bring them for independent review and author approval before
   freezing them and building the proof dependency graph.

See [Phase 1](docs/PROJECT-OUTLINE.md#phase-1--fix-the-one-loop-calculation).

## Repository map

| Path | Role |
| --- | --- |
| [README.md](README.md) | Campaign HQ: purpose, current state, progress, and next actions |
| [docs/WHAT-IS-PROVED.md](docs/WHAT-IS-PROVED.md) | What a proved QED calculation certifies, from model and rules to experimental comparison |
| [docs/PROJECT-OUTLINE.md](docs/PROJECT-OUTLINE.md) | Scientific and implementation outline |
| [docs/ORCHESTRATOR-LAUNCH.md](docs/ORCHESTRATOR-LAUNCH.md) | Reusable launch prompt, first assignment, delegation, review gates, and reporting |
| [docs/SOURCES.md](docs/SOURCES.md) | Pinned primary, secondary, and background sources, with hashes and coverage |
| [docs/CONVENTIONS.md](docs/CONVENTIONS.md) | Metric, units, Dirac algebra, spinors, Feynman rules, form factors, and the mostly-minus dictionary |
| [docs/REGULARIZATION.md](docs/REGULARIZATION.md) | Regulator comparison and choice, the Minkowski-integral prescription, renormalization, and order of limits |
| [docs/ONE-LOOP-DERIVATION.md](docs/ONE-LOOP-DERIVATION.md) | Source-linked derivation from the interaction to the magnetic moment, with numbered proof obligations |
| [docs/MATHLIB-INVENTORY.md](docs/MATHLIB-INVENTORY.md) | What Mathlib `v4.35.0` provides and what the pilot must build |
| [docs/campaign/STATUS.md](docs/campaign/STATUS.md) | Current state, validation, and next work |
| [docs/campaign/DECISIONS.md](docs/campaign/DECISIONS.md) | Decisions, author rulings, and pending questions |
| [docs/campaign/FINDINGS.md](docs/campaign/FINDINGS.md) | Source errata, gaps, and deviations with evidence |
| [docs/campaign/progress.json](docs/campaign/progress.json) | Milestones, statuses, and completion evidence |
| [sources/manifest.json](sources/manifest.json) | URLs, sizes, SHA-256 hashes, and licenses of pinned sources (bytes not committed) |
| [lakefile.lean](lakefile.lean), [lean-toolchain](lean-toolchain), [QED.lean](QED.lean) | Lean package `qed`, pinned to Lean and Mathlib `v4.35.0` |
| [QED/Frozen/](QED/Frozen) | Author-approved frozen declarations and their [manifest](QED/Frozen/manifest.json); immutable, checked by the frozen-anchor guard |
| [QED/Provider/](QED/Provider) | Proof providers for frozen theorem goals; quarantined until the goal is sealed |
| [QED/Integration/](QED/Integration) | Proved analysis: the loop-energy integrals by analytic continuation to the slit plane, which replaces Wick rotation (`EnergyIntegral.lean`) |
| [QED/Algebra/](QED/Algebra) | Proved infrastructure: the mostly-plus Minkowski form (`Minkowski.lean`), the Weyl Dirac matrices (`Dirac.lean`), gamma-matrix products and the Gordon identity (`Gordon.lean`), the contraction identities (`Contraction.lean`), and on-shell spinors (`Spinor.lean`) |
| [scripts/update_hq.py](scripts/update_hq.py) | Render or check the progress meters |
| [scripts/fetch_sources.py](scripts/fetch_sources.py) | Fetch and verify the pinned source bytes |
| [scripts/check_frozen_anchors.py](scripts/check_frozen_anchors.py) | Frozen-anchor guard (verbatim from the lean-orchestrator skill) |
| [scripts/frozen_abi.py](scripts/frozen_abi.py) | Recompute and check elaborated ABI hashes of frozen exports |
| [scripts/numerics/one_loop_sanity.py](scripts/numerics/one_loop_sanity.py) | Floating-point sanity checks of the one-loop algebra (not proofs) |
| [AGENTS.md](AGENTS.md) | Scope, integrity rules, and shared-machine conventions |
| [LICENSE](LICENSE) | Apache License, Version 2.0 |

Certificate datasets will be added when their first concrete contents are
ready.

## Build and validation

```bash
lake build                                  # every module under QED/; reuses cached Mathlib
python3 scripts/update_hq.py --check        # HQ consistency (not a proof check)
python3 scripts/fetch_sources.py            # verify pinned source bytes
python3 scripts/numerics/one_loop_sanity.py # numerical sanity checks (not proofs)
python3 scripts/check_frozen_anchors.py --root . --manifest QED/Frozen/manifest.json
python3 scripts/frozen_abi.py --check        # elaborated ABI hashes of frozen exports
```

`lake build` prints no warnings. The frozen-anchor guard fails on any `sorry`
not registered as a `DRAFT_SORRY` body (none is registered at present), on any
change to frozen bytes, on a sealed body other than `by exact <provider export>`,
and on any import of a draft anchor or its provider outside the allowlist.

Every regular `.lean` file must be a Lean module. Landings run the
`lean-project-architecture` skill's `check_lean_modules.py --root .`. On this
shared machine, use niced, focused builds, and never `lake clean`. The Mathlib
dependency tree must come from the cache or a local copy, never a rebuild; see
decision D-3 in the [decision log](docs/campaign/DECISIONS.md).

## License

The project's own files are licensed under the
[Apache License, Version 2.0](LICENSE) (decision D-10). The pinned
third-party source documents listed in [docs/SOURCES.md](docs/SOURCES.md) are
not part of the repository; their own terms apply.
