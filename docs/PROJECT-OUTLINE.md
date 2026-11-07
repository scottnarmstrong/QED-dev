# Project outline: verified QED calculations

[Campaign HQ](../README.md) · [Progress ledger](campaign/progress.json)

**Established:** 2026-11-07. **Status:** initial outline; no exact Lean
declarations or regulator prescription have been approved or frozen.

## 1. Purpose and first target

Build a Lean 4 development that helps physicists calculate experimentally
testable quantities. The initial observable is the electron's anomalous magnetic
moment,

$$a_e=\frac{g_e-2}{2}.$$

The first complete result is the one-loop Schwinger correction. The subsequent
targets are the complete two-loop contribution, selected higher-loop families,
and eventually the five-loop QED contribution used in precision predictions.
Infrastructure is developed to serve these calculations, with numerical
certification treated as part of the project from the beginning.

The initial formulation is perturbative QED. Constructing a complete
nonperturbative continuum QED model is a separate mathematical problem and is
not a prerequisite for certifying the finite-order calculations defined here.

## 2. What the prediction contains

Write $r=\alpha/\pi$. A finite-order prediction has the form

$$P_N(\alpha,\rho)=\sum_{n=1}^{N}C_n(\rho)r^n,$$

where $\rho$ records the relevant lepton-mass ratios. For the first coefficient,
$C_1=1/2$. The precision comparison also needs hadronic and electroweak
contributions, uncertainty in physical inputs, and an assessment of omitted
contributions. Each must be represented separately in the eventual result.

There are four distinct claims:

| Claim | Required evidence |
| --- | --- |
| A coefficient is derived correctly | A theorem from the defined perturbative model to the coefficient |
| Its value lies in an interval | A theorem bounding the defining renormalized integral, with certificate validation |
| A truncation approximates a fuller quantity | An explicit remainder theorem or a clearly identified external estimate |
| A prediction agrees with an experiment | A sourced dataset and a specified uncertainty and comparison procedure |

Coefficientwise formal equality is not a bound on a perturbative remainder.
Likewise, a Monte Carlo confidence statement is not a deterministic interval
theorem. The campaign must preserve these distinctions in its statements and HQ.

## 3. First complete theorem

The one-loop target is the coefficient $C_1=1/2$ of the **independently defined**
renormalized magnetic form factor, together with its magnetic-moment
interpretation. This paragraph describes the intended mathematics; it is not a
Lean declaration or a frozen statement.

The calculation must connect:

1. The chosen regularized perturbative QED model and interaction conventions.
2. The order-$e^2$ correction to the electron-photon vertex, including the diagram
   coefficient and fermionic conventions.
3. On-shell spinor identities and extraction of the Pauli form factor $F_2$.
4. Justified parameterization, loop integration, and regulator removal.
5. The coefficient $C_1=1/2$, or equivalently the one-loop value
   $F_2^{(1)}(0)=\alpha/(2\pi)$.
6. The magnetic coupling showing that, with charge normalization $F_1(0)=1$,
   the anomaly is $F_2(0)$ in the perturbative formulation.

The last step needs a stated low-momentum/external-field interpretation and its
proof. Naming a scalar expression after the observable is insufficient.
Defining the coefficient as the known answer is also insufficient.

The numerical evaluation of the resulting coefficient and its contribution for
an input interval for $\alpha$ is a separate, linked deliverable. One loop
demonstrates the leading correction; it does not establish modern experimental
precision.

## 4. Campaign phases

### Phase 0 — establish HQ

Create the repository, outline, working rules, and evidence-based progress
meters. This phase is documentation and tooling work, with no mathematical
completion credited to it. The ledger records the initial deliverables.

### Phase 1 — fix the one-loop calculation

Select a full modern derivation and record its exact version, sections,
equations, bibliographic information, and content hash. Schwinger's original
paper identifies the target but does not by itself supply the detailed modern
derivation required for implementation.

Make a convention sheet covering metric signature, gamma matrices, spinor and
Fourier normalizations, charge sign, units, on-shell conditions, momentum
transfer, vertex normalization, and the definition of $\alpha$.

Compare at least the plausible regulator routes for this calculation and select
one using a small mathematical feasibility study. Specify the UV and IR
treatments, renormalization conditions, order of limits, and gauge choice.
Dimensional regularization, if selected, needs a precise algebraic and
meromorphic interpretation; a noninteger dimension is not an ordinary
finite-dimensional integration space.

Write out the mathematical derivation and expose the conditions needed for
changes of variables, shifts of loop momentum, Wick rotation where used,
interchange of limits and integrals, and cancellation of singular terms.
Record unresolved steps as proof obligations.

Inventory the relevant Mathlib APIs, then choose and pin compatible modular
Lean/Mathlib revisions. PhysLib is a reference for architecture and coverage,
not an imported dependency. Any later dependency change must be deliberate.

Develop the exact source-facing Lean definitions and theorem statements. Review
their carriers, bodies, hypotheses, and connection to the observable. Obtain
author approval before freezing actual declarations. Only then construct a
source-level proof graph anchored to those declarations. This outline is not
such a graph.

**Exit:** pinned derivation and conventions, a justified route, a reproducible
Lean environment, and reviewed exact declarations with an explicit dependency
plan. No source-facing claim is counted as proved at this point.

### Phase 2 — complete one loop

Develop the algebra and analysis needed by the fixed calculation, in small
modules. Prove the vertex expression, form-factor extraction, integral
transformations, finiteness and limits, exact coefficient, and magnetic-moment
interpretation. Construct the final theorem from those results.

The ledger separates eight milestones so that the final coefficient evaluation
cannot conceal a missing amplitude derivation or observable interpretation.
Helpers are useful progress, but the scientific milestone requires the whole
chain and an independent statement/source review.

**Exit:** the complete one-loop result builds at the recorded revision, has the
intended statement, and passes source, hypothesis, and axiom audits. The exact
declaration and validation record are linked from HQ.

### Phase 3 — certify numerical evaluation

Develop exact or rigorously rounded arithmetic and integral-enclosure theorems
as required by the pilot. External programs may discover substitutions, integral
reductions, partitions, or quadrature data. Their output is evidence to be
checked against independently defined mathematical semantics.

A checker must have a soundness theorem: accepted data implies the stated
enclosure for the specified integral. Its validation must include rejection of
invalid certificates. General certificate infrastructure should be separated
from coefficient-specific data.

For higher-dimensional integrals, plan for endpoint singularities, analytic
tail or boundary bounds, cancellation, and conditioning. Investigate certified
domain decompositions and regularized representations before committing to
large numerical runs. If randomized integration is used, formalize the stated
probabilistic guarantee and its assumptions separately.

**Exit:** a reproducible coefficient certificate and numerical contribution
bound for the pilot, derived from the same amplitude as Phase 2. Certified
high-dimensional integration remains a later research task.

### Phase 4 — complete two loops

Enumerate all contributions under the selected conventions. Extend the
renormalization framework to the required subtractions, counterterms, and
cancellations; prove the relevant identities at their correct stage. Derive the
complete coefficient, including the specified mass-dependent contributions,
and certify its evaluation.

**Exit:** a complete two-loop result, with checked enumeration and all assembly
dependencies accounted for, using APIs that can support a higher-loop pilot.

### Phase 5 — certify higher-loop families

Select a published, bounded family with explicit integrands and a meaningful
comparison target, preferably a gauge-invariant set. Pin the exact source and
data, including corrections. Validate a small sample before scaling.

Extend verified diagram enumeration, renormalization, symbolic reductions, and
integral certification. Establish the relationship between any computational
intermediate scheme and the final stated renormalization prescription.
Independent agreement is useful diagnostic evidence; equality or enclosure
claims still require their own proofs.

Advance from a complete family to broader coverage. Full five-loop completion
requires all contributions in scope, including the relevant lepton loops and
mass dependence. A certified subset must be reported as a subset.

**Exit:** first a certified published family, and eventually complete five-loop
QED coefficient coverage with reproducible evidence. These are distinct results.

### Phase 6 — assemble an experimental comparison

Create versioned input records for $\alpha$, mass ratios, experimental results,
and non-QED corrections. Record units, uncertainty conventions, correlations,
and provenance. An $\alpha$ inferred from the same electron anomaly must not be
presented as an independent test of that prediction.

Propagate inputs and coefficient enclosures through a proved evaluation of
$P_N$. Attach hadronic and electroweak contributions at the required precision,
with their actual verification status. Keep any assumption or estimate for
omitted orders explicit rather than absorbing it into numerical roundoff.

Define the experimental comparison procedure and state which uncertainties are
deterministic bounds, statistical quantities, or external theory estimates.
Publish the exact resulting claim and its inputs. A disagreement is a valid
possible outcome of the comparison.

**Exit:** a reproducible comparison at a stated order and precision, with every
component of its uncertainty budget visible. A stronger full-theory accuracy
claim requires correspondingly stronger remainder and external-input results.

## 5. Proposed implementation areas

The following names describe responsibilities, not existing directories or
frozen module interfaces. Introduce modules when their first real contents are
ready and adjust boundaries after the Mathlib inventory.

| Proposed area | Responsibility |
| --- | --- |
| `QED/Algebra/` | Clifford and spinor algebra; proved symbolic normalization |
| `QED/Perturbation/` | Formal orders, interaction expansion, diagrams, signs, and multiplicities |
| `QED/Amplitudes/` | Regularized amplitudes and justified transformations |
| `QED/Renormalization/` | Subtractions, counterterms, scheme relations, and cancellations |
| `QED/Observables/` | Form factors, magnetic coupling, and anomaly extraction |
| `QED/Integration/` | Analytic integral results, convergence, and regulator limits |
| `QED/Numerics/` | Enclosures, certificate formats, checkers, and soundness |
| `QED/ElectronG2/` | Assembly of loop-order and family-specific results |
| `QED/Comparison/` | Prediction evaluation and uncertainty propagation |
| `docs/` | Sources, conventions, decisions, progress, and validation reports |
| `certificates/` | Versioned computational data with provenance and replay instructions |
| `scripts/` | Lightweight maintenance and certificate-generation tools |

Keep source-facing definitions and approved theorem anchors distinct from proof
implementation. Draft anchors, if introduced under the freezing workflow, must
be quarantined and cannot count as proved dependencies. Every regular Lean
source must use the module system.

## 6. Acceptance and progress rules

- A source-facing result must mean the intended physics claim on its stated
  carrier. Audit bundled structures as well as visible theorem hypotheses.
- Physical model postulates, imported mathematics, retained external inputs,
  and proof obligations have distinct roles. An intermediate result is not
  promoted into a postulate to make a proof compile.
- Only exact author-approved Lean declarations can be frozen. A Markdown target
  or planning approval does not freeze a declaration.
- A completed formal milestone needs the actual Lean export, a recorded build,
  source/statement review, and an axiom audit. Accepted completed results use
  only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Drafts and conditional helpers are labeled with their actual scope. They do
  not complete a stronger target. No theorem is completed through `sorry`.
- Certificate generation and mathematical checking are separate. Record the
  exact data, checker revision, semantics, and replay command.
- Update the ledger with evidence when a milestone is completed. Record any
  change to milestone scope in its history. The meters count milestones with
  equal weight within each row; there is no overall effort percentage.
- The status script checks documentation consistency, not theorem validity.
  Its success must never be described as a Lean build or a physics audit.

## 7. Initial source candidates

These links identify starting material. They are not yet a pinned source
archive or an endorsement of every intermediate derivation.

1. **Schwinger (1948), On Quantum-Electrodynamics and the Magnetic Moment of the
   Electron.** Historical target and first coefficient.
   [DOI](https://doi.org/10.1103/PhysRev.73.416).
2. **Aoyama, Hayakawa, Kinoshita, Nio (2012), Quantum electrodynamics calculation
   of lepton anomalous magnetic moments: Numerical approach to the perturbation
   theory of QED.** Computational architecture, renormalization, and numerical
   integration. [DOI](https://doi.org/10.1093/ptep/pts030).
3. **Fan, Myers, Sukra, Gabrielse (2023), Measurement of the Electron Magnetic
   Moment.** Experimental observable and input-dependence of its theory test.
   [Preprint, version 2](https://arxiv.org/abs/2209.13084v2).
4. **Aoyama, Hayakawa, Hirayama, Nio (2025), Verification of the tenth-order QED
   contribution to the anomalous magnetic moment of the electron from diagrams
   without fermion loops.** Diagram comparison and the importance of numerical
   validation. [Preprint, version 3](https://arxiv.org/abs/2412.06473v3).
5. **Volkov (2024), Calculation of the total 10-th order QED contribution to the
   electron magnetic moment.** An independent higher-loop computational route.
   [Preprint, version 2](https://arxiv.org/abs/2404.00649v2).
6. **PhysLib.** Reference for formal physics architecture and Wick combinatorics;
   not a dependency. The initial discussion inspected commit
   `4e2182f2b6f0a54207a2fa62002c264217f875d6`.
   [Repository snapshot](https://github.com/leanprover-community/physlib/tree/4e2182f2b6f0a54207a2fa62002c264217f875d6).

Phase 1 must add a full one-loop derivation, pin the selected material, and
record exact equation-level provenance. Later literature and input datasets
must be checked again when the corresponding phase begins.
