# Certificates

This directory records computational data that Lean's kernel checks: what the data is, what it
means, which checker reads it, and how to reproduce it. Generating the data and checking it are
separate steps. The generator scripts are not trusted. If a certificate is wrong or has been
tampered with, the kernel check fails; it cannot produce a false theorem. The data is stored as
Lean modules under `QED/Numerics/Certificates/` so that `lake build` checks it.

## Pauli enclosures (packet Q; decisions D-34, D-35)

**Theorems served.** These certificates prove packet Q's (Q₁), (Q₂) and (Q₃). Take
`m_γ = m/10ᵏ`, `Λ = 10ᵏ m` for `k = 1, 2, 3`, and `q² = m²/10⁴`. Then every form-factor pair
of the one-loop vertex has `F₂ = (e²/8π²) t`, with `t` in `[0.7668, 0.7673]`,
`[0.9700, 0.9705]` and `[0.9966, 0.9971]` respectively.

**Semantics.** Let `a = 10⁻ᵏ` and `c = 10⁻⁴`. Put `Q = 1 + x(1 - x)c` and
`T_K = y²/((1 - y)K + y²Q)`. Each certificate encloses the integral of

    g(x, y) = 2(1 - y)(1 - T_{a²} + T_{1/a²})

against `QED.Integration.feynmanMeasure`, which is Lebesgue measure on `(0, 1]²`. For every
`m ≠ 0`, `QED.Numerics.Pauli.integral_pauliIntegrand_eq` gives

    t = ∫ pauliIntegrand m (m a, m/a, m² c) = 1 - ∫ g.

So the claim `∫ g ∈ [1 - t_hi, 1 - t_lo]` gives `t ∈ [t_lo, t_hi]`.

| k | data module | boxes | claim for `∫ g` | checker's enclosure of `∫ g` | kernel time | peak RSS |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `QED/Numerics/Certificates/PauliTen.lean` | 5105 | `[0.2327, 0.2332]` | `[0.232825891, 0.233075849]` | 8.5 s | 3.2 GB |
| 2 | `QED/Numerics/Certificates/PauliHundred.lean` | 772 | `[0.0295, 0.0300]` | `[0.029622452, 0.029872299]` | 1.2 s | 2.0 GB |
| 3 | `QED/Numerics/Certificates/PauliThousand.lean` | 107 | `[0.0029, 0.0034]` | `[0.003009899, 0.003258385]` | 0.1 s | 1.8 GB |

- The enclosures are rounded outward. Each lies inside its claim with at least `1.0·10⁻⁴` to
  spare.
- Reference values of `∫ g` are `0.232953657`, `0.029750538` and `0.003132211`. They come from a
  30-digit `mpmath` quadrature and are not part of the certificate.
- Kernel time is the profiler's `type checking` time for one `decide +kernel` check. Peak RSS is
  for the `lean` process checking that one certificate, and includes about 1.7 GB
  for the imports.

**Format.** Each data module defines two objects.

- `pauli<P>Cuts : List ℕ` lists the cut heights `n` in increasing order. Each cut stands for
  `y = n/2⁶⁴`, and the list ends at `2⁶⁴`.
- `pauli<P>Partition : List QED.Numerics.Strip` equals `[⟨2⁶⁴, pauli<P>Cuts⟩]`. This is a
  single strip `x ∈ (0, 1]`, cut into the boxes `(y_{i-1}, y_i]` starting from `y_0 = 0`.

Both are `noncomputable`, because the kernel does not need compiled code.

**Checker.**

- `QED.Numerics.Quadrature.check` in `QED/Numerics/BoxQuadrature.lean` runs on the integer
  interval arithmetic `QED.Numerics.Interval` from `QED/Numerics/Interval.lean`. Its soundness
  theorem is `QED.Numerics.Quadrature.integral_bounds_of_check_of_continuousOn`.
- `QED/Numerics/PauliExtension.lean` contains the interval extension
  `QED.Numerics.Pauli.remExt` of `g`, its soundness theorem `remExt_sound`, and the combined
  theorem `integral_pauliIntegrand_mem_of_check`.
- `QED/Numerics/PauliEnclosures.lean` contains the kernel checks `check_ten`, `check_hundred`
  and `check_thousand`. Each runs `decide +kernel` at scale `2⁶⁴` with `KA = ofRat a²`,
  `KB = ofRat a⁻²` and `C = ofRat 10⁻⁴`. The same module derives the enclosures
  `integral_pauliIntegrand_ten`, `_hundred` and `_thousand`, and the reduction
  `isFormFactorPair_vertexOneLoop_pauli_mem` that the providers use.

**Revision.**

- `Interval.lean` and `BoxQuadrature.lean` are used unmodified as of commit
  `88abfe7a07bf8daa9d0beef1708ec2ceeeb86394` (git blobs `d5c1c06f` and `636647f4`).
- `PauliExtension.lean` (blob `0f45ab59`), `PauliEnclosures.lean` (blob `eb8bd577`), the
  generator (blob `c3388d2a`) and the data were added in the same change as this file.
- SHA-256 of the data modules:
  - `PauliTen.lean`: `3e340488d2d9ac7e07c1ac6a0c9b15610a94c45407c9829e8eed6a090c9e8515`
  - `PauliHundred.lean`: `d2d68c6d250a5164fcd5aa402b51155066f89714dae8b219a9bf6f2b512013f5`
  - `PauliThousand.lean`: `471789e1b30b72e881e2e7fa19ace41fd0c08ab36dc983664e0d88ce5846d130`

**Generation.** The data comes from `scripts/numerics/gen_pauli_certificates.py`. The script
uses Python 3 and only the standard library, and runs in under a second.

- It starts from geometric cuts `2⁴⁰, …, 2⁶³, 2⁶⁴` and bisects in `y` greedily. Each step
  splits the segment whose split narrows the enclosure most, until the enclosure is narrower
  than `2.5·10⁻⁴`.
- It evaluates `remExt` with an exact integer copy of `QED.Numerics.Interval`, using the same
  operations and the same outward rounding. It therefore predicts the kernel's sums exactly.
  A scratch check at `k = 3` confirmed this: the kernel accepted a claim equal to the predicted
  sums and rejected the claim made one unit tighter at either end.
- All its arithmetic is on integers, so the output is deterministic.

**Replay.** From the repository root:

```sh
python3 scripts/numerics/gen_pauli_certificates.py --check  # regenerate in memory, compare bytes
python3 scripts/numerics/gen_pauli_certificates.py          # or rewrite the data modules,
git diff --exit-code QED/Numerics/Certificates              # and confirm that nothing changed
nice -n 5 lake build QED.Numerics.PauliEnclosures           # kernel checks: about 10 s, 3 GB
```
