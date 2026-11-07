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

**Current state:** campaign documentation and progress tooling are initialized.
There is no Lean implementation, pinned toolchain, or proved physics result yet.

**Start here:** [What does "proved" mean?](docs/WHAT-IS-PROVED.md) ·
[Project outline](docs/PROJECT-OUTLINE.md) ·
[Orchestrator launch](docs/ORCHESTRATOR-LAUNCH.md) ·
[Immediate next steps](#next-steps) · [Progress data](docs/campaign/progress.json) ·
[Working rules](AGENTS.md)

## Progress

The meters count completed, explicitly listed milestones. They measure neither
effort nor experimental precision, and they are not an estimate of how much of
QED has been formalized. Campaign setup is kept separate from mathematical work.
The longer-term milestone lists will be refined as their sources and statements
become precise; changes to their scope must be recorded.

<!-- HQ:progress:start -->
**Ledger updated:** 2026-11-07. Only milestones marked `done` contribute to the meters.

| Workstream | Complete | Milestone meter | State |
| --- | ---: | --- | --- |
| Campaign setup | 4/4 | `██████████` 100% | Complete |
| Sources and exact specification | 0/4 | `░░░░░░░░░░` 0% | Planned |
| Complete one-loop calculation | 0/8 | `░░░░░░░░░░` 0% | Planned |
| Numerical certification pilot | 0/4 | `░░░░░░░░░░` 0% | Planned |
| Complete two-loop calculation | 0/4 | `░░░░░░░░░░` 0% | Planned |
| Higher loops toward five-loop QED | 0/4 | `░░░░░░░░░░` 0% | Planned |
| Experimental comparison | 0/4 | `░░░░░░░░░░` 0% | Planned |

**Tracked Lean source files:** 0. Documentation milestones do not count as proved physics.
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

1. Select and pin a full modern derivation of the one-loop magnetic moment;
   record conventions and any gaps in its textbook manipulations.
2. Compare regulator and renormalization routes, choose one for the pilot, and
   write the mathematical derivation with all required conditions exposed.
3. Inventory Mathlib, choose compatible Lean/Mathlib revisions, and initialize
   the Lean package. PhysLib is a design reference, not a project dependency.
4. Develop the exact source-facing Lean definitions and theorem statements for
   review before freezing them and constructing the proof dependency graph.

The immediate task is **source and semantic specification**, followed by the
first bounded proof tasks. See [Phase 1](docs/PROJECT-OUTLINE.md#phase-1--fix-the-one-loop-calculation).

## Repository map

| Path | Role |
| --- | --- |
| [README.md](README.md) | Campaign HQ: purpose, current state, progress, and next actions |
| [docs/WHAT-IS-PROVED.md](docs/WHAT-IS-PROVED.md) | What a proved QED calculation certifies, from model and rules to experimental comparison |
| [docs/PROJECT-OUTLINE.md](docs/PROJECT-OUTLINE.md) | Scientific and implementation outline |
| [docs/ORCHESTRATOR-LAUNCH.md](docs/ORCHESTRATOR-LAUNCH.md) | Reusable launch prompt, first assignment, delegation, review gates, and reporting |
| [docs/campaign/progress.json](docs/campaign/progress.json) | Milestones, statuses, and completion evidence |
| [scripts/update_hq.py](scripts/update_hq.py) | Render or check the progress meters |
| [AGENTS.md](AGENTS.md) | Scope, integrity rules, and shared-machine conventions |

Lean source directories, source archives, and certificate datasets will be added
when their first concrete contents are ready. They are not present in this
documentation bootstrap.
