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

[The computation](docs/THE-COMPUTATION.md) explains, for non-specialists, what
$a_e$ is, why each loop order is harder, and how far the verification has come.

**Where things stand.**

- **One loop: done.** Starting from the rules of QED with the standard (on-shell)
  mass and charge conditions, Lean proves Schwinger's result: the electron's
  $g$-factor is $2(1+\alpha/2\pi)$ at this order.
- **Two loops: done.** Lean proves the exact two-loop coefficient,
  $\frac{197}{144}+\frac{\pi^2}{12}-\frac{\pi^2}{2}\ln2+\frac34\zeta(3)
  =-0.328\,478\,965\ldots$ (Petermann and Sommerfield, 1957), and the
  smaller contributions from muon and tau loops.
- **Three loops: in progress.** The target is the exact result of Laporta and
  Remiddi (1996), which sums 72 Feynman diagrams in five groups. One group is
  proved. For two more, the final integrals are proved equal to their published
  values, and the link back to the underlying model is being built. The two
  largest groups (56 diagrams) are not yet started.

Every theorem is checked by Lean's kernel using only Lean's standard axioms.
The one- and two-loop main results were also re-checked by two independent
proof checkers. [The computation](docs/THE-COMPUTATION.md) explains these
results in more detail; the [campaign status](docs/campaign/STATUS.md) has the
working detail.

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
**Ledger updated:** 2026-11-19. Only milestones marked `done` contribute to the meters.

| Workstream | Complete | Milestone meter | State |
| --- | ---: | --- | --- |
| Campaign setup | 4/4 | `██████████` 100% | Complete |
| Sources and exact specification | 4/4 | `██████████` 100% | Complete |
| Complete one-loop calculation | 8/8 | `██████████` 100% | Complete |
| Numerical certification pilot | 4/4 | `██████████` 100% | Complete |
| Complete two-loop calculation | 4/4 | `██████████` 100% | Complete |
| Complete three-loop calculation | 2/9 | `██░░░░░░░░` 22% | In progress |
| Higher loops toward five-loop QED | 0/4 | `░░░░░░░░░░` 0% | Planned |
| Experimental comparison | 0/4 | `░░░░░░░░░░` 0% | Planned |

**Tracked Lean source files:** 1471. **Total lines of Lean code:** 312,072.
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
areas, completion criteria, and initial sources. These are planning targets, not Lean
declarations. The exact Lean statements are fixed stage by stage: those of the one-loop
result are approved and frozen; for two loops, the model is approved and frozen, and the
target constant, the one-loop Ward identity and the headline statement are approved and
frozen (decisions D-39 to D-41, approved in D-43).

**Scope of the two-loop headline.** The two-loop headline theorem is a statement about the
one-particle-irreducible electron–photon vertex at order $e^5$, with the one-loop counterterms
fixed by the on-shell and charge conditions: its magnetic form factor $F_2$ tends to
$e^4A_1^{(4)}/(16\pi^4)$ in the stated order of regulator limits. It does not include the
order-$e^5$ vertex counterterm or the two-loop external-leg factors, which $F_2$ does not need;
without them the order-$e^5$ electric form factor $F_1$ is not renormalized. Lifting the result to
the measured magnetic moment through the model's own LSZ amplitude, as the one-loop headline does,
needs counterterms graded by order and is future work (decisions D-37, D-44).

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

## Errata and deviations

Checking the calculation formally turned up five misprints in the primary
source. The most visible are a sign in the denominator of the Pauli form
factor (63.21) and a reversed wave-packet width condition on p. 383; the
formal definitions use the corrected forms. The formal route also departs
deliberately from the source in a few places: Pauli–Villars regularization
with energy-first loop integrals instead of dimensional regularization,
including regulator fermions for the closed fermion loop of the vacuum
polarization; an external photon treated as a background field, whose leg
keeps the vacuum-polarization insertion; and two magnetic-moment definitions
proved equivalent instead of an asserted quantum action. Each item is
documented with its evidence in
[ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md).

## Next steps

- **Finish three loops.** Complete the model for three-loop diagrams, link the
  three groups whose values are already proved back to it, and then compute
  the two remaining groups: the six light-by-light diagrams and the fifty
  diagrams without closed electron loops.
- **Then four and five loops.** These are the later phases of the
  [outline](docs/PROJECT-OUTLINE.md#4-campaign-phases), together with a
  comparison with the measured value of $a_e$.

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
| [docs/TWO-LOOP-DERIVATION.md](docs/TWO-LOOP-DERIVATION.md) | The two-loop plan: enumeration, divergences, route, exact evaluation, and numbered proof obligations for the fourth-order coefficient |
| [docs/HIGHER-LOOP-PLAN.md](docs/HIGHER-LOOP-PLAN.md) | The Phase 5 plan for higher-loop families: candidate families, the recommended first family (vacuum-polarization chains) and the mass-dependent two-loop term, route, obligations and open design questions |
| [docs/MATHLIB-INVENTORY.md](docs/MATHLIB-INVENTORY.md) | What Mathlib `v4.35.0` provides and what the pilot must build |
| [docs/campaign/STATUS.md](docs/campaign/STATUS.md) | Current state, validation, and next work |
| [docs/campaign/DECISIONS.md](docs/campaign/DECISIONS.md) | Decisions, author rulings, and pending questions |
| [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md) | Errors found in the sources and how the formal route departs from them |
| [docs/campaign/FINDINGS.md](docs/campaign/FINDINGS.md) | Source errata, gaps, and deviations with evidence |
| [docs/campaign/progress.json](docs/campaign/progress.json) | Milestones, statuses, and completion evidence |
| [sources/manifest.json](sources/manifest.json) | URLs, sizes, SHA-256 hashes, and licenses of pinned sources (bytes not committed) |
| [lakefile.lean](lakefile.lean), [lean-toolchain](lean-toolchain), [QED.lean](QED.lean) | Lean package `qed`, pinned to Lean and Mathlib `v4.35.0` |
| [QED/Frozen/](QED/Frozen) | Author-approved frozen declarations and their [manifest](QED/Frozen/manifest.json); immutable, checked by the frozen-anchor guard |
| [QED/Provider/](QED/Provider) | Proof providers for frozen theorem goals; quarantined until the goal is sealed |
| [QED/OneLoop/](QED/OneLoop), [QED/Wick/](QED/Wick), [QED/WickModel/](QED/WickModel) | Proved helper modules: the one-loop vertex, form factors and magnetic moments; the order-e³ Wick expansion; the general model with regulator fermions, the self-energy and vacuum polarization, the LSZ amplitude, and the headline assembly |
| [QED/Numerics/](QED/Numerics), [certificates/](certificates) | Certified numerics: integer interval arithmetic, the box-partition quadrature checker with its soundness theorem, the Pauli form-factor certificates, and their provenance and replay |
| [QEDChallenge.lean](QEDChallenge.lean), [QEDSolution.lean](QEDSolution.lean), [comparator.json](comparator.json) | Comparator challenge: a Mathlib-only statement of the headline theorem and its proof from the library |
| [QEDChallengeTwoLoop.lean](QEDChallengeTwoLoop.lean), [QEDSolutionTwoLoop.lean](QEDSolutionTwoLoop.lean), [challenges/two-loop/comparator.json](challenges/two-loop/comparator.json) | Two-loop Comparator challenge: the two-loop headline, the integrability of every term and the enclosure of A₁⁽⁴⁾, stated over Mathlib only, with their proofs from the library |
| [QED/Integration/](QED/Integration) | Proved analysis: the loop-energy integrals by analytic continuation to the slit plane, which replaces Wick rotation (`EnergyIntegral.lean`) |
| [QED/Algebra/](QED/Algebra) | Proved infrastructure: the mostly-plus Minkowski form (`Minkowski.lean`), the Weyl Dirac matrices (`Dirac.lean`), gamma-matrix products and the Gordon identity (`Gordon.lean`), the contraction identities (`Contraction.lean`), and on-shell spinors (`Spinor.lean`) |
| [scripts/update_hq.py](scripts/update_hq.py) | Render or check the progress meters |
| [scripts/fetch_sources.py](scripts/fetch_sources.py) | Fetch and verify the pinned source bytes |
| [scripts/check_frozen_anchors.py](scripts/check_frozen_anchors.py) | Frozen-anchor guard (from the lean-orchestrator skill; accepts `sorry` only in the Comparator Challenge) |
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
not registered as a `DRAFT_SORRY` body, on any change to frozen bytes, on a sealed
body other than `by exact <provider export>`, and on any import of a draft anchor or
its provider outside the allowlist. Two `DRAFT_SORRY` bodies are registered at present: the sixth-order set (b) headline (HC₃) and its
integrability companion (HC₀), of the Phase 5 Stage 1a packet (decision D-53); their proofs are in
progress. The packet's other six goals are proved and sealed. Every earlier frozen theorem is sealed, including the two-loop headline with heavy
leptons (HM₂) (decision D-51). The two-loop headline theorem (decisions D-41, D-43, D-46) and its companion (HV₀),
that every term of the order-$e^5$ vertex is a genuine integral (decision D-45), are proved and
sealed.

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
