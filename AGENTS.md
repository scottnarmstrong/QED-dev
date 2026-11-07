# Working in QED-dev

## Purpose and current scope

Read [campaign HQ](README.md) and the [project outline](docs/PROJECT-OUTLINE.md)
before starting work. The priority is experimentally relevant QED computation,
beginning with the complete one-loop electron magnetic anomaly. Develop reusable
infrastructure in service of that target.

This initial repository contains documentation and HQ maintenance tooling.
Lean/Mathlib revisions, exact declarations, and the regulator route remain to be
selected. Do not describe the documentation bootstrap as a Lean implementation.

## Mathematical integrity

- Use the relevant Lean architecture, workflow, and statement-audit skills.
- Choose and pin mathematical sources and conventions before fixing the
  source-facing declarations. Only actual exact Lean declarations can be
  reviewed, author-approved, and frozen; Markdown plans do not qualify.
- Inspect meaning-carrying definitions, bundled assumptions, and operator
  domains. Prove intermediate steps rather than adding them as assumptions.
- Keep formal coefficients, numerical enclosures, asymptotic bounds, and
  empirical comparisons distinct. Label retained external inputs explicitly.
- Source-facing definitions must already denote the intended objects. For
  characterization-defined objects, prove existence and uniqueness before
  defining the object from that result.
- Completed formal results require source/statement review, a reproducible
  build, and an axiom audit. Only standard Lean axioms are accepted.
- Any draft `sorry` anchors allowed by the freezing workflow are unproved and
  quarantined. Production proofs may not depend on them.
- Use Lean's module system for every regular `.lean` source. Audit dependency
  compatibility before pinning the toolchain and Mathlib.
- PhysLib is a design reference, not an imported dependency.

## HQ and evidence

Update `docs/campaign/progress.json`, then run `python3 scripts/update_hq.py`.
Do not edit the generated progress block directly. Run the script with
`--check` before committing. Mark a milestone done only with linked evidence;
formal milestones additionally require a Lean artifact and validation record.
The script checks consistency, not mathematical validity.

Keep campaign setup separate from proof completion. Record milestone scope
changes in the ledger history. Add build commands and validation details to HQ
when a real Lean package exists.

## Shared machine and repository hygiene

- This is lemma.farm, a shared machine. Explain expensive commands before
  running them and avoid unnecessary CPU, memory, and disk use.
- Prefer focused builds and existing dependency caches. Never run `lake clean`
  as routine maintenance or rebuild all of Mathlib unnecessarily.
- Do not modify other campaigns, their caches, or another session's work.
- Keep generated computational data separate from hand-written proofs and
  record its provenance and replay instructions.
- Do not install background updaters or schedule recurring work unless asked.
