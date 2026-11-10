# Campaign status

[Campaign HQ](../../README.md) · [Decisions](DECISIONS.md) · [Findings](FINDINGS.md) ·
[Progress ledger](progress.json)

**As of 2026-11-09.** Phase 1 (fix the one-loop calculation). Packets 1–5, 6a and 6b are proved and audited: the vertex is derived from the order-e³ Wick expansion, g → 2(1 + α/2π) for both magnetic-moment definitions, and the general Wick model fixes the counterterms δ₂, δ_m and δ₃ by the on-shell conditions. Packet 6c (the LSZ amplitude, D-29) and the headline theorem (L1.ASSEMBLY, D-21) remain.

Milestones (see the [ledger](progress.json)):

| Milestone | Status |
| --- | --- |
| SPEC.SOURCE, SPEC.ROUTE, SPEC.ENV | done, on the evidence below |
| SPEC.STATEMENTS | in progress: packets 1, 1b, 2, 3, 4a, 4b, 5, 6a, 6b-1, 6b-2, 6c-1, 6c-2, and the headline packet approved and frozen (D-11, D-12, D-14, D-15, D-16, D-18, D-20, D-24, D-26, D-27, D-28, D-30, D-31, D-33) |
| L1.MODEL | in progress: algebra infrastructure and the entrywise algebra of the frozen vertex integrand |
| L1.PROJECTION | done: the decomposition (63.18) of the one-loop vertex exists and is unique (packet 2, (G)) |
| L1.INTEGRAL | done: the closed form of the one-loop vertex, and its well-definedness (E) |
| L1.LIMITS, L1.COEFFICIENT | done for the (62.40) diagram under D-5: F₂ → e²/8π² = α/2π, so C₁ = 1/2, jointly as q², m_γ → 0⁺ and Λ → ∞ (packet 2, (I)) |
| L1.OBSERVABLE | done: both magnetic-moment definitions of D-9, their equivalence O-24, and g → 2(1 + α/2π) for each (packets 4a and 4b) |
| L1.VERTEX | done: the order-e³ 1PI part of the Wick expansion with all counterterms is iZ₁eγ^μ plus the regulated (62.40) diagram (O-1, O-2), and its ε → 0⁺ limit is the vertex function (packet 5) |
| L1.ASSEMBLY | planned, design decided (D-21, D-22, D-23): one headline theorem from the Wick vertex; O-3 as the full LSZ amplitude, with Σ, Π (Pauli–Villars regulator fermions) and the on-shell conditions, in a general successor of the Wick model; fresh-checkout audit, Comparator challenge, errata ledger |

## Reporting fields

```text
DRAFT_ANCHORS: 2 — QED/Frozen/WickModel/LszFormFactorExistsUnique.lean (H₀′),
               QED/Frozen/WickModel/LszAmplitudePauliLandeFactorLimit.lean (H)
UNREGISTERED_SORRIES: 0 (scripts/check_frozen_anchors.py: FROZEN-ANCHOR GUARD OK)
DRAFT_IMPORT_VIOLATIONS: 0 (same guard run)
SEALED_THIS_TURN: 0
```

| Field | Value |
| --- | --- |
| Model / prescription | Perturbative QED in Feynman gauge with the on-shell scheme, starting from a momentum-space Wick expansion at order $e^3$ (D-8). The one-loop pilot uses a Pauli–Villars photon (mass $\Lambda$) and a photon mass $m_\gamma$, with Minkowski loop integrals defined by the energy-first prescription M1 ([REGULARIZATION.md](../REGULARIZATION.md); D-5). The magnetic moment has two definitions, the source's wave-packet definition and the vertex response, proved equivalent (D-9). |
| Base commit for this work | `67a0e50`. The landing commits follow it on `main`. |
| Retained external inputs | none. No conditional results exist. |
| Proved source-facing results | (E) `QED.OneLoop.vertexLimit_existsUnique`: the regulated one-loop vertex is well defined. (F′) the characterization of the one-loop vertex `QED.OneLoop.vertexOneLoop`. (G) `existsUnique_isFormFactorPair_vertexOneLoop`: for e ≠ 0 and q² > 0 the decomposition (63.18) exists and is unique. (I) `isFormFactorPair_vertexOneLoop_pauli_limit`: near q², m_γ → 0⁺ and Λ → ∞, every form-factor pair has F₂ within η of e²/8π² = α/2π, uniformly over the momenta. Packet 3: (K) the charge condition (63.1) fixes a unique counterterm Z₁; (N) the counterterm shifts only F₁ (O-8); (M) F₁(0) = 1 (64.2) at fixed regulators. Packet 4a: (R) the response magnetic moment exists and is unique; (R′) with the charge-normalized counterterm, g = 4mμ/e → 2(1 + α/2π) (64.17) jointly as m_γ → 0⁺ and Λ → ∞. Packet 4b: (W₄) for the source's wave-packet definition (64.4)–(64.9), the undamped position integral converges absolutely and, as the packet narrows, the source μ tends to the response μ (O-24); (W₅) g → 2(1 + α/2π) for the source definition. Scope: the (62.39) vertex function under D-5, with current matrix elements read from the amputated vertex (O-3). Packet 5: (W₁) the order-e³ 1PI part of the Wick expansion with all counterterms is iZ₁eγ^μ plus the regulated (62.40) diagram, with coefficient one and no closed-loop sign (O-1, O-2); (W₂) its ε → 0⁺ limit is the vertex function. Packet 6a: (Y₁) packet 5 is a special case of the general Wick model with Pauli–Villars regulator fermions. Packet 6b: (Z₁), (Z₂) the one-loop self-energy and vacuum polarization exist in covariant form; (Z₆), (Z₉) the on-shell conditions (62.27) and (62.11) fix δ₂, δ_m and δ₃ uniquely. Packet 6c-1: (L₁) the LSZ amplitude of the electron current exists and is unique. Packet 6c-2: (L₃) it equals ū′V^μu plus a photon-leg term e·q²D(q²)Π(q²)ū′γ^μu; (L₄′), (L₅′), (L₇′) the charge condition and both magnetic-moment definitions restated with the LSZ amplitude are equivalent to packets 3, 4a and 4b. The assembled theorem (L1.ASSEMBLY) remains. |
| Pending author decisions | None open. Rulings so far: D-1, D-8, D-9, D-10, D-11, D-12, D-14, D-15, D-16, D-17, D-18, D-19, D-20, D-21, D-22, D-23, D-24, D-25, D-26, D-27, D-28, D-29, D-30, D-31, D-32, and D-33 (headline packet, approved 2026-11-10). |

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
  - F-10: a units convention in a background source (not an erratum).
  - F-11: a source erratum (the wave-packet width on p. 383), verified twice.
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
- **More infrastructure** (2026-11-08):
  - `QED/Algebra/SpinorBoost.lean`: the closed-form spinors equal the source's
    boosted rest spinors exp(iη p̂·K)u_s(0) (38.12), for p⃗ ≠ 0.
  - `QED/OneLoop/ChargeRenormalization.lean`:
    - on shell, the loop's γ^μ coefficient depends only on q²;
    - at p′ = p the loop sandwich is e·A(0)·ū′γ^μu;
    - A(q²) is continuous at q² = 0⁺ at fixed regulators.

    These are the analytic facts behind packet 3 (charge renormalization),
    which is drafted and independently reviewed.
- **Packet 1's theorem (E) proved** (2026-11-08). The proof is in
  [`QED/Provider/OneLoop/VertexLimitExists.lean`](../../QED/Provider/OneLoop/VertexLimitExists.lean),
  and the frozen anchor is sealed by it (D-13 records the provider's binder
  convention). Route, for each fixed $\epsilon>0$:
  - the four denominators are combined with Feynman parameters over the unit
    square (O-5, `QED/Integration/FeynmanParameter.lean`);
  - Fubini is applied on $\mathbb R\times[0,1]^2$, and the energy integral is
    evaluated in closed form (O-6, `QED/Integration/ShiftedEnergyIntegral.lean`);
  - the Pauli–Villars difference is bounded by $C(1+\|\vec\ell\|)^{-5}$,
    uniformly in $\epsilon$.

  The bound holds because the Feynman mass term satisfies
  $D\ge\frac34\min(M^2,m^2)$, using $m_\gamma>0$ and $q^2\ge0$ on shell
  (`QED/OneLoop/VertexAlgebra.lean`, `QED/Algebra/OnShell.lean`). Dominated
  convergence, applied twice, gives the limit (O-10).

  The supporting modules were written by three parallel workers with exact
  target statements; the uniform bounds (`QED/Integration/LoopBounds.lean`) and
  the assembly were written by the orchestrator. An independent refute-first
  audit found no defect. It confirmed:
  - the frozen bytes and the ABI hash;
  - that the statement elaborates identically with only the frozen
    definitions imported;
  - that the provider's type is `Expr.eqv` to the frozen type after erasing
    `autoParam`;
  - that only the standard axioms are used, including a `leanchecker` replay;
  - that every helper premise is discharged;
  - that the mathematics holds when checked by hand.
- **Infrastructure toward packet 2** (2026-11-08). This is proved infrastructure,
  not source-facing results.
  - `QED/OneLoop/VertexEnergyFirst.lean`: the analysis of (E), moved out of
    the provider (which is now a short assembly), together with:
    - the limit representation `∫ v, spatialG 0 v`;
    - the boundary values $(-W)^{-3/2}=iW^{-3/2}$ and $(-W)^{-5/2}=-iW^{-5/2}$;
    - the uniform bound at $\epsilon=0$.
  - `QED/OneLoop/VertexClosedForm.lean`: the Fubini swap at $\epsilon=0$, and the
    $x\leftrightarrow1-x$ symmetry of the Feynman measure.
  - `QED/Integration/SpatialIntegral.lean`:
    $\int d^3v\,(v^2+D)^{-5/2}=4\pi/(3D)$; the Pauli–Villars log integral
    $2\pi\ln(D_2/D_1)$; vanishing odd moments; isotropy of second moments.
  - `QED/OneLoop/NumeratorReduction.lean`: the $d=4$ contraction of the
    numerator, and its on-shell reduction (63.14)–(63.17). The $(p'-p)^\mu$
    coefficient is odd under $x\leftrightarrow1-x$.
  - `QED/OneLoop/VertexSpatial.lean`, `VertexFormFactors.lean`, and
    `PauliLimit.lean`:
    - the closed form
      $(1/i)\lim=\frac{e^3}{16\pi^2}\int dF_3\,[\ln(D_\Lambda/D_{m_\gamma})\gamma^\mu+\tilde N^\mu/(2D_{m_\gamma})-\tilde N^\mu/(2D_\Lambda)]$;
    - its sandwich between on-shell Dirac solutions, which equals
      $e\,\bar u'[A\gamma^\mu-\frac im BS^{\mu\nu}q_\nu]u$ with explicit $A$ and
      $B=\frac{e^2}{8\pi^2}\int dF_3\,(x_3-x_3^2)m^2(1/D_{m_\gamma}-1/D_\Lambda)$
      (`sandwich_vertexLimit`);
    - the joint limit of the normalized $B$, which is $1$ as $m_\gamma\to0^+$,
      $\Lambda\to\infty$, $q^2\to0^+$ (`tendsto_integral_pauliIntegrand`),
      also in $\epsilon$–$\delta$ form.

    These are the analytic contents of packet 2's goals (G) (existence) and
    (I). The proofs of (G) and (I) remain to be assembled once packet 2 is
    approved and frozen.
  - `QED/Algebra/FormFactorIndependence.lean`: gamma traces, and the
    independence of $\bar u'\gamma^\mu u$ and $\bar u'S^{\mu\nu}q_\nu u$ for
    $q^2>0$ (the uniqueness half of O-15).
- **Frozen declarations** (D-11, D-12; [`QED/Frozen/manifest.json`](../../QED/Frozen/manifest.json)).
  - Packet 1: the regulated propagators, the (62.40) integrand, the
    energy-first integral, and the theorem (E), now sealed and proved.
  - Packet 1b: `metric`, `dot`, `lower`, `gamma`, and `slash`, moved into
    frozen files with unchanged names and unchanged elaborated meaning.
  - Every definition closure is transitive over frozen files. The guard
    therefore protects packet 1's meaning down to Mathlib.
  - Correction to a project document found while pinning packet 1b:
    CONVENTIONS.md cited (36.9) for the slash. The definition is (37.24),
    p. 238; (36.9) only gives $\not p\not p=-p^2$.
- **Author rulings recorded** (D-8, D-9). The model starts from a
  momentum-space Wick expansion. Both magnetic-moment definitions will be
  formalized and proved equivalent. The derivation's stages 0 and 5 and its
  carrier table are updated, and obligation O-24 (equivalence) is added.

## Validation

| Check | Command | Result |
| --- | --- | --- |
| Baseline environment | `lake build --no-build` after copying the dependency tree | Mathlib and its dependencies up to date; no rebuild |
| Transient import probe | `lake env lean` on an untracked module importing the focused sets (file deleted) | 26/26 sampled inventory names elaborate; all loaded from cache in under 5 s |
| Project build | `nice -n 5 lake build` | success; 2918 jobs; no warnings |
| Module system | `check_lean_modules.py --root .` (lean-project-architecture skill) | PASS (244 Lean files) |
| Axioms | `#print axioms` on all 58 theorems and lemmas in `QED/` at the earlier landing; on 2026-11-08 on `QED.OneLoop.vertexLimit_existsUnique`, its provider, and every exported theorem of the five new modules (transient files, deleted) | only `propext`, `Classical.choice`, `Quot.sound` |
| Forbidden tokens | grep for `sorry`, `admit`, `axiom`, `maxHeartbeats`, `native_decide` over `QED/` and `QED.lean` | none |
| Source bytes | `python3 scripts/fetch_sources.py` | 5/5 OK |
| Numerical sanity (not proofs) | `python3 scripts/numerics/one_loop_sanity.py` | all eight checks pass |
| HQ consistency (not a proof check) | `python3 scripts/update_hq.py --check` | run at each landing |
| Frozen-anchor guard | `python3 scripts/check_frozen_anchors.py --root . --manifest QED/Frozen/manifest.json` | `FROZEN-ANCHOR GUARD OK` (10 anchors); rejected all eight negative tests: at packet 1, a statement edit, a body edit, an unregistered `sorry`, a draft import, and a provider import; at packet 1b, a `metric` body edit (also reported as closure drift downstream), a whitespace-only docstring edit, and a second declaration in a frozen file |
| Frozen ABI hashes | `python3 scripts/frozen_abi.py --check` | 10/10 OK. For packet 1b, `pp.all` output of each definition was byte-identical before and after the move. |
| Independent audit of packet 4a | refute-first auditor, not the prover | (R), (R′) PROVED. Frozen bytes and moved definitions match; statements are equal; standard axioms; μ and Z₁ derived; e = 0 and non-vacuity checked by Lean witnesses; Breit identities checked numerically |
| Independent audit of packet 3 | refute-first auditor, not the prover | (K), (N), (M) PROVED. Frozen bytes match the approved text; statements are equal; standard axioms; Z₁ = 1 − A(0) derived; (M) shown non-vacuous by a Lean witness |
| Independent audit of packet 2 | refute-first auditor, not the prover | (F′), (G), (I) PROVED. Frozen bytes match the approved text; `pp.all` statements are equal with only the frozen definitions imported; provider types are equal up to `autoParam`; standard axioms only; no smuggled premise. B at m_γ = 0, Λ = ∞ matches (63.20) to 8 digits. Only documentation-lag nits, addressed before landing |
| Independent audit of (E) | refute-first auditor, not the prover | PROVED: frozen bytes and ABI hash unchanged; the statement elaborates identically with only the frozen definitions imported; standard axioms (also replayed with `leanchecker`); no smuggled premise; the mathematics checked by hand. Its nits were addressed before landing (docstring, line length, lemma placement) |
| Independent document review | refute-first reviewer (not the writer). It checked SOURCES, CONVENTIONS, REGULARIZATION, and ONE-LOOP-DERIVATION against the pinned PDFs: about 45 Srednicki citations, the dictionary and conventions numerically, and the integrals, bounds, and limits | No wrong source citation and no sign or normalization error in the load-bearing chain. 16 findings, all addressed before landing: 3 errors (an asymptotic stated for $n=1$; the remainder term of the photon-mass deficit; leg corrections listed as parts of the 1PI $V^\mu$), 5 weak claims, 8 nits |

A documentation check is not a Lean build. A floating-point check is not a
proof.

## Remaining obligations and next bounded tasks

1. **Packet 6c is complete (D-29, D-30, D-31).** The LSZ amplitude is
   defined, its closed form proved, and the charge condition and both
   magnetic-moment definitions are restated with it and shown equivalent to
   packets 3, 4a and 4b.
2. **L1.ASSEMBLY (D-21, D-32).** The headline theorem, stated from the
   general Wick model with on-shell counterterms and the LSZ amplitude: F₂
   within η of α/2π and both Landé factors within η of 2(1 + α/2π) near the
   regulator limit. Frozen (D-33); proofs ready, audit pending. Then the
   Comparator challenge and the fresh-checkout audit.
3. **Cleanups.** Land the closed form δ₃ = (e²/12π²)Σ_f c_f log M_f² as a
   lemma; remove unused helpers and duplicated lemmas noted in audits.
