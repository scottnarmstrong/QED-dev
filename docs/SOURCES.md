# Sources

[Campaign HQ](../README.md) · [Conventions](CONVENTIONS.md) ·
[Regularization](REGULARIZATION.md) · [One-loop derivation](ONE-LOOP-DERIVATION.md) ·
[Findings](campaign/FINDINGS.md)

**Status (2026-11-07):** primary and secondary sources selected and pinned
(decision D-6). Pinning fixes the exact bytes that later reviews compare
against. It does not endorse every step of a source: the gaps and misprints
are recorded in the [findings ledger](campaign/FINDINGS.md).

## How the bytes are pinned

The repository is public, and most of these documents may not be
redistributed. The PDFs are therefore not committed (decision D-2).
[`sources/manifest.json`](../sources/manifest.json) records each URL,
retrieval time, size, SHA-256, and license. Run

```bash
python3 scripts/fetch_sources.py --fetch   # download into sources/cache/ and verify
python3 scripts/fetch_sources.py           # verify an existing cache
```

The script checks bytes only. A server may regenerate a file (arXiv does,
and the Kaplunovsky notes were regenerated in 2024). A mismatch is then
reported, and the change must be reviewed before the new bytes are used.
`sources/cache/` is listed in `.gitignore`.

All five files listed below were verified against these hashes on 2026-11-07.

## Primary source

**M. Srednicki, *Quantum Field Theory*, prepublication draft** (`srednicki-draft`).

| Field | Value |
| --- | --- |
| Version | Author's prepublication draft, PDF created 2006-10-13; 616 pages; server Last-Modified 2007-10-29 |
| URL | `https://web.physics.ucsb.edu/~mark/ms-qft-DRAFT.pdf` (linked from `https://web.physics.ucsb.edu/~mark/qft.html`) |
| Retrieved | 2026-11-07T17:38:08Z |
| Size / SHA-256 | 3452472 bytes / `7990bad06ed96750f742729bcc65292f169589739af29012bb110b70649b5621` |
| License | All rights reserved. The file asks readers not to distribute it and to link to the author's page instead. |
| Published edition | Cambridge University Press, 2007, ISBN 0521864496. Equation numbers agree with the draft; page numbers in chapters 62–64 are about 7–8 higher. The author's errata list refers to the published pagination. |

Page numbers below are PDF pages, which equal the printed draft pages.

| Chain item | Draft location |
| --- | --- |
| Metric | (2.1)–(2.4), p. 30 |
| Units $\hbar=c=1$, Heaviside–Lorentz, $e<0$ | (58.1), p. 345 |
| Feynman's formula, Wick rotation, master integral (tools) | (14.9)–(14.11), (14.16), (14.27), pp. 111–114 |
| Gamma matrices, Weyl representation, Clifford relation | (36.7)–(36.9), p. 227 |
| Spinors, normalization, Gordon identity | (38.1)–(38.21), pp. 240–242 |
| Lorentz generators $S^{\mu\nu}$ | (40.3), p. 254 |
| LSZ for spinors | (41.1)–(41.29), pp. 263–267 |
| LSZ to Feynman rules (Yukawa example) | (45.11)–(45.16), pp. 285–286 |
| Contraction identities | (47.18)–(47.21), p. 297 |
| LSZ for photons | (56.1)–(56.8), p. 339 |
| Lagrangian, gauge invariance, path integral, Feynman rules | (58.1)–(58.21) and rules 1–12, pp. 345–350 |
| Counterterms, $R_\xi$ gauge, vacuum polarization | (62.1)–(62.25), pp. 369–372 |
| Self-energy, photon mass, residue conditions | (62.26)–(62.38), pp. 372–375 |
| One-loop vertex function | (62.39)–(62.50), pp. 375–377 |
| Charge condition, on-shell reduction, form factors, $F_2(0)=\alpha/2\pi$ | (63.1)–(63.22), pp. 378–382 |
| General vertex structure (exercise) | problem 63.1, (63.23), p. 382 |
| Magnetic moment, $g=2(1+\alpha/2\pi)$ | (64.1)–(64.17), pp. 383–385 |

**Why this source.** Of the freely retrievable sources examined, it is the
only one that covers the whole chain in one set of conventions:

- the Lagrangian;
- the path-integral derivation of the Feynman rules;
- LSZ, with the unit-residue external lines;
- the one-loop vertex;
- the on-shell charge condition;
- the reduction to $F_1,F_2$;
- the result;
- a magnetic-moment interpretation with an explicit definition of $\mu$ (64.7).

Its core algebra (63.10)–(63.20) was checked numerically by the source worker,
independently of the text. The orchestrator checked the on-shell reduction
separately: the coefficient $(1-2x_3-x_3^2)m^2$ in (63.14) agrees with an
independent derivation and with
[`scripts/numerics/one_loop_sanity.py`](../scripts/numerics/one_loop_sanity.py)
after translation (CONVENTIONS.md, section 7).

**Known limitations** (details in the [findings ledger](campaign/FINDINGS.md)):

- Five misprints in or near the chain: (56.6), (63.6), p. 380, and (63.21),
  which appear in the author's published errata (F-3 to F-6), and the
  wave-packet width condition on p. 383, which does not (F-11). See
  [ERRATA-AND-DEVIATIONS.md](ERRATA-AND-DEVIATIONS.md).
- The UV regulator is dimensional; the project uses Pauli–Villars (F-2).
- Several steps are left to exercises or to "the usual manipulations" (F-7).
- The magnetic-moment step passes through an asserted quantum-action form
  (64.3) and a defined interaction Hamiltonian (64.6) (F-8).

## Secondary source

**[V. Kaplunovsky], "QED Vertex Correction"**, course notes, University of Texas
at Austin, Fall 2012 (`kaplunovsky-vertex`).

| Field | Value |
| --- | --- |
| URL | `https://web2.ph.utexas.edu/~vadim/Classes/2012f/vertex.pdf` |
| Retrieved | 2026-11-07T17:39:46Z |
| Size / SHA-256 | 146868 bytes / `701e6894bfc50ba5ddfc051f12ae000f20a3283e5fb87e00110a4370ceeffa59` |
| License | None stated; treated as not redistributable |
| Caveats | No author or date is printed; the attribution comes from the URL. The PDF was regenerated on 2024-09-10. It uses mostly-minus conventions and is written as a companion to Peskin–Schroeder §6. |

**Role.** It fills the steps the primary source leaves out:

- Feynman parametrization and the shift, (8)–(15), pp. 2–4;
- symmetric integration in $D$ dimensions, (28)–(29), p. 7;
- an explicit Wick rotation and radial integral, (40), p. 9;
- the full on-shell reduction, (21)–(27), pp. 5–7;
- $F_2(0)=\alpha/2\pi$, (41)–(43), p. 9;
- keeping Feynman gauge with a photon mass, (62)–(65), p. 15;
- the counterterm $\delta_1$, (76)–(81), pp. 17–18.

Two misprints are recorded as F-9.

## Background sources (pinned, not load-bearing)

| ID | Citation | Use | Size / SHA-256 | License |
| --- | --- | --- | --- | --- |
| `ahkn-2012` | T. Aoyama, M. Hayakawa, T. Kinoshita, M. Nio, *Prog. Theor. Exp. Phys.* 2012, 01A107, doi:10.1093/ptep/pts030. INSPIRE copy, retrieved 2026-11-07T17:39:26Z | Magnetic projection (4.2)–(4.4), p. 12; numerical higher-loop architecture | 1102124 / `0a2e1df91a8390a25783982dd5435d17804bb7a26609cc044c59d00bff57fa91` | CC BY 3.0. This copy carries per-page library download stamps, so obtain clean publisher bytes before relying on page images. |
| `knecht-2003` | M. Knecht, *Lect. Notes Phys.* 629 (2004) 37–84, arXiv:hep-ph/0307239v1, retrieved 2026-11-07T17:39:44Z | Trace projectors (2.14)–(2.15), pp. 5–6; gauge-parameter independence of $F_2$, p. 11; one-loop result (4.1)–(4.5) | 423162 / `0b82943d67eb0354267ac5fa5dfa81374a9a702ef648da5edf00a9b4b9d48c56` | arXiv license; not redistributable |
| `liu-mit-8324-l15` | H. Liu, MIT OCW 8.324 (Fall 2010), Lecture 15, retrieved 2026-11-07T17:39:46Z | Nonrelativistic reduction to the Pauli equation, giving $g=2+2F_2(0)$, (3)–(11), pp. 1–2 | 170260 / `4bf21df5c5e65c7ff8b1b5e901b1d24d7e154ca505f8fbb79d6053b1df8b045b` | CC BY-NC-SA 4.0 |

## Background references (not pinned)

- J. Schwinger, *Phys. Rev.* 73 (1948) 416, doi:10.1103/PhysRev.73.416: the
  historical result. It is not a modern derivation.
- M. Peskin and D. Schroeder, *An Introduction to Quantum Field Theory*
  (Addison-Wesley, 1995), §§6.2–6.3: the standard textbook treatment. Not
  retrieved, so no page or equation references are claimed.
- M. Schwartz, *Quantum Field Theory and the Standard Model* (Cambridge, 2014),
  ch. 17. Not retrieved.
- W. Zimmermann, *Commun. Math. Phys.* 11 (1968) 1–8: the absolutely convergent
  Minkowski prescription M2 ([REGULARIZATION.md](REGULARIZATION.md)). Not
  retrieved; pin it before relying on it.
- F. Jegerlehner and A. Nyffeler, *Phys. Rept.* 477 (2009) 1, arXiv:0902.3360v1
  (SHA-256 `285594c721d849dc525523a41f07de1c1aefff0f0887744eec465ca8aeb70651`
  as retrieved 2026-11-07), and B. Lynch, arXiv:hep-ph/0108081v3
  (`72675f0a99e35c5e05c42fe4d24917c249ea8cf534c371dac9b99e26930718cc`): checked
  during selection; useful only for cross-checks.
- The remaining [initial candidates](PROJECT-OUTLINE.md#7-initial-source-candidates)
  in the outline concern later phases and the experimental comparison.
