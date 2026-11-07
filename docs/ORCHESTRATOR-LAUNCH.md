# Launching the QED-dev orchestrator

[Campaign HQ](../README.md) · [Project outline](PROJECT-OUTLINE.md) ·
[What a proof certifies](WHAT-IS-PROVED.md)

Use the following prompt to start a new orchestrator session. It authorizes the
preparation work described below, including bounded delegation and routine
commits and pushes. Writing this launch brief does not itself launch agents.

## Launch prompt

```text
Work in /home/scott/QED-dev as the campaign orchestrator.

Read AGENTS.md, README.md, docs/PROJECT-OUTLINE.md,
docs/WHAT-IS-PROVED.md, docs/campaign/progress.json, and this entire file,
docs/ORCHESTRATOR-LAUNCH.md. Inspect the checkout and existing campaign records
before deciding what to do next. The files and current Git state take precedence
over this launch brief's initial-state description.

Use the lean-orchestrator and lean-project-architecture skills, and the other
Lean/source-audit skills when their tasks become applicable.

Start with Phase 1: make the complete one-loop electron magnetic-anomaly
calculation mathematically precise and ready for exact-statement review.
Select and pin a full derivation, settle the conventions and computational
prescription, expose every substantive proof obligation, inventory Mathlib,
and initialize a compatible pinned Lean environment. Prepare the exact
source-facing declarations as soon as their real carriers and definitions
are available. Follow the approval and freezing rules below.

Proceed autonomously with research, ordinary implementation choices,
reversible setup, and validated infrastructure. Use independent workers for
bounded research and reviews when useful; keep source interpretation, shared
interfaces, and integration under your control. Do not substitute planning
documents, assumed intermediate results, or a supplied final integral for
the intended model-to-observable calculation.

Keep HQ and its evidence ledger current. Commit and push coherent, checked
landings to this development repository, preserving other sessions' work.
Continue useful independent work while a specific question is pending.
Bring the author a concrete review packet when exact statement approval is
needed. Report actual results, remaining obligations, and validation evidence.
```

## Mission and initial state

The first scientific target is the complete one-loop result
$[r]F_2(0;r)=1/2$, with $r=\alpha/\pi$, together with the magnetic-moment
interpretation giving $a_e^{(1)}=\alpha/(2\pi)$. This is a mathematical target,
not an approved Lean declaration. The longer campaign serves experimentally
relevant QED calculations, including higher-loop coefficients and certified
numerics.

At the time this brief was written, the repository had only documentation and
HQ maintenance tooling. There was no Lean package, pinned mathematical source
archive, regulator decision, frozen declaration, proof graph, or proved physics
result. Check the live repository before relying on that description. Resume
existing work rather than creating competing sources of truth.

The first assignment is to make the one-loop calculation precise. Work on the
actual QED derivation; develop auxiliary examples only when they resolve a
specific dependency or feasibility question for that calculation.

## First actions

1. Read the files named in the prompt, repository history, active ledgers, and
   any later instructions. Inspect `git status --short --branch` before editing.
   Identify existing work and its owner; preserve it.
2. Run `python3 scripts/update_hq.py --check`. This verifies HQ consistency,
   not mathematics. Inspect available Lean tooling and dependency caches
   without initiating a broad build.
3. State the current preparation tasks, the next bounded deliverable, and any
   actual uncertainty. Inspect resource use before announcing expensive work.
4. Begin source selection and a dependency inventory. Delegate only independent
   tasks with explicit ownership and outputs. Keep research workers build-free.

## Phase 1 deliverables

Create these records as their contents become concrete; do not create empty
forms or duplicate an existing equivalent record.

| Record | Required content |
| --- | --- |
| `docs/SOURCES.md` | Selected primary derivation, exact version, retrieval information, content hash, and equation/page ranges; distinguish background references |
| `docs/CONVENTIONS.md` | Metric, units, coupling sign and normalization, spinors, gamma matrices, Fourier conventions, momenta, external-leg normalization, and form factors |
| `docs/REGULARIZATION.md` | A reasoned route choice, UV/IR definitions, renormalization conditions, gauge treatment, order of limits, and a bounded feasibility argument |
| `docs/ONE-LOOP-DERIVATION.md` | Source-linked mathematics from interaction expansion to magnetic response, with every substantive transformation and unresolved obligation exposed |
| `docs/MATHLIB-INVENTORY.md` | Exact existing declarations and paths at the inspected revision, missing mathematics, and focused implementation dependencies |
| `docs/campaign/DECISIONS.md` | Decisions actually made, their reasons and scope, and author rulings when required |
| `docs/campaign/FINDINGS.md` | Source gaps, convention differences, and candidate errors with exact evidence and review status |
| `docs/campaign/STATUS.md` | Current state, concrete validation, next work, and the reporting fields below |

Pin source bytes and record their hashes, not just a mutable URL. A historical
statement of Schwinger's answer is not a full derivation. Check that the chosen
source covers the amplitude, projection, normalization, and magnetic response;
record and supply mathematical arguments where it skips steps. Distinguish
project proof obligations from defects in the source. Independently verify any
claimed erratum before presenting it as an established source error.

Compare plausible regulator routes, then choose the best justified bounded
route for the pilot. Record ordinary choices and proceed; ask the author about
genuine changes of scientific scope or unresolved physical meaning. Preserve
the treatment of singular integrals and distributions. A finite projected
integral is a useful intermediate object only when its connection to the QED
amplitude is also established.

Select compatible modular Lean/Mathlib revisions based on the inventory and
available caches. Pin them, initialize the actual package, and record a small
reproducible baseline check. Use real definitions and proved infrastructure;
avoid sample theorems or placeholders that resemble scientific progress.
PhysLib remains a design reference, not an imported dependency.

## Exact declarations and the approval gate

The repository's [Phase 1 rule](PROJECT-OUTLINE.md#phase-1--fix-the-one-loop-calculation)
states: **"Obtain author approval before freezing actual declarations."** This
gate protects the meaning of the physics being formalized. It is not a request
for permission to do routine research or implementation.

Before requesting approval, complete all independent preparation needed for a
reviewable result. Bring the author:

- The selected source and a concise explanation of the actual model and route.
- The complete exact Lean commands: imports, explicit/implicit/instance
  binders, conclusion, and the full bodies of meaning-carrying definitions.
- Source/binder/definition review by someone who did not write the commands,
  together with elaboration evidence and unresolved findings.
- A precise statement of what approval would freeze and why approval is needed.
  Cite the repository rule and the exact applicable skill instruction.

Only declarations whose carriers and definitions already have their intended
meaning can be submitted. Check pre-approval commands in transient, untracked
files and remove them afterward. Do not commit candidate declarations, tracked
probes, fallback definitions, or a Markdown surrogate for the mathematical
interface. If genuine infrastructure is missing, develop it and identify the
remaining dependency; do not invent an easier carrier to manufacture a packet.

If a source defines an object by a unique characterization, first address the
exact existence-and-uniqueness theorem. Prove it before introducing the object
from that theorem, and land its definition with its full proved
characterization. Literal source formulas can be defined directly after review.

Approval of this launch, an outline, or a subject area does not approve unseen
Lean declarations. While approval is pending, continue source work and
independent infrastructure. Do not cross the dependent freezing gate.

## After approval: proofs and integration

Select a small anchor surface: the headline result, essential intermediate
theorems, and definitions that determine their meaning. Freeze approved
declarations before extracting their source-level proof graph or assigning
downstream proof work.

Use the installed skill's manifest and quarantine machinery. Approved unproved
theorem anchors may have only the registered body `by sorry`, in
one-declaration frozen files. Record source identity, export, frozen bytes and
hashes, provider, and draft state. Establish the guards before admitting these
files. Definitions never use this exception. Every draft anchor and its
registered provider remain quarantined from other consumers until sealing.

Independently review the anchored dependency graph. Assign bounded proofs from
its dependency-ready frontier. Each graph edge is an obligation to prove and
consume a result, not permission to add that result as a theorem hypothesis.

Providers prove the exact targets without importing draft anchors. Seal through
the registered proof body only, then check the frozen export, source fidelity,
actual dependency consumption, compilation, and axioms. A fresh reviewer must
audit the result before it is marked proved. A defective frozen declaration
requires an author-approved versioned successor and invalidation of dependent
evidence; never weaken it silently.

## Delegation and machine resources

During preparation, use at most two concurrent workers in addition to the
orchestrator, and respect the session's actual lower limit if applicable.
Useful separate tasks are source transcription, Mathlib discovery, and an
independent review after the relevant writing is complete. Give each worker:

```text
Goal: one bounded result.
Ownership: specific files or a read-only review; no other edits.
Inputs: exact sources, conventions, and approved/proved dependencies.
Target: exact anchor identity if one exists; otherwise label this preparation.
Checks: named validation commands and required evidence.
Stop: report a precise mathematical or API obstruction; do not alter scope.
Hard rules: preserve frozen declarations and source meaning; add no hidden
premises or unauthorized axioms/placeholders; every regular .lean file is a
module; obey the campaign's compile gate and shared-machine rules.
Handoff: files or commit, approach, checks/results, unresolved issues, and scope.
```

Inspect every worker's diff and evidence. Keep HQ, common interfaces, route
decisions, and landings under the orchestrator's ownership. Reviews compare
directly against pinned sources and exact declarations; the writer does not
serve as the independent reviewer.

Initially serialize compilation across this campaign. When parallel builds
become useful, use the lean-orchestrator skill's compile-gate workflow with
campaign-specific scope, account for other users' load, and reserve capacity
for integration. Explain expensive commands before running them. Avoid global
toolchain changes that affect other sessions; adapt the gate to an isolated
campaign toolchain if necessary.

Workers run at most one targeted, niced build at a time. Reuse dependency caches
and supported copy-on-write snapshots when available; never share writable
artifacts through hardlinks. Do not run `lake clean` or rebuild Mathlib as
routine maintenance. Resource contention is a reason to measure, limit builds,
and continue independent work. Record interrupted checks as incomplete.

## Status, validation, and landings

Keep the milestone ledger and HQ synchronized. Mark preparation tasks
`in_progress` when work has actually begun and `done` only with complete
evidence. Statement preparation is not complete while required approval is
outstanding. Formal completion requires Lean evidence, validation records, and
the actual mathematical checks; HQ's script supplies none of those proofs.

Every campaign status report must include:

```text
DRAFT_ANCHORS: count and paths, or 0 / none after inspection
UNREGISTERED_SORRIES: count and paths, or 0 / none after inspection
DRAFT_IMPORT_VIOLATIONS: count and paths, or 0 / none after inspection
SEALED_THIS_TURN: count and exact exports
```

Also identify the model/prescription, current commit, work completed, validation
commands and results, retained external inputs or conditional results, pending
author decisions, and the next bounded task. Do not turn unchecked claims into
zero counts or report a partial integral evaluation as a complete QED result.

Before each landing, inspect the staged diff, run `git diff --cached --check`
and `python3 scripts/update_hq.py --check`, and check local documentation links.
When Lean files exist, also run the module and relevant freeze/quarantine
guards, focused builds, and required axiom/source audits. A documentation-only
check is not a Lean build. Stage explicit paths and preserve unrelated changes.
Commit and push coherent validated changes to the existing development remote;
do not change visibility, publish a release, or install scheduled jobs as part
of this launch.

The first run should leave concrete Phase 1 evidence and a clear next action.
If exact declarations are ready, present their review packet for the required
approval. If they are not ready, identify the real missing mathematics and
advance the available work. The aim is a sound route into the calculation,
with progress measured by what has actually been established.
