# One-loop derivation: from the interaction to the magnetic moment

[Campaign HQ](../README.md) · [Sources](SOURCES.md) · [Conventions](CONVENTIONS.md) ·
[Regularization](REGULARIZATION.md) · [Mathlib inventory](MATHLIB-INVENTORY.md) ·
[Findings](campaign/FINDINGS.md) · [Decisions](campaign/DECISIONS.md)

**Status (2026-11-07):** source-linked derivation plan with its proof obligations
exposed. Nothing here is a Lean declaration, and nothing has been approved,
frozen, or proved. Equation numbers $(n.m)$ and page numbers refer to the
primary source `srednicki-draft`; "K($n$)" refers to equation $(n)$ of the
secondary source `kaplunovsky-vertex`. Notation and the project's deviations
follow [CONVENTIONS.md](CONVENTIONS.md) and
[REGULARIZATION.md](REGULARIZATION.md): mostly-plus metric, $e<0$,
$q=p'-p$, a Pauli–Villars photon with mass $\Lambda$ and photon mass $m_\gamma$,
and loop integrals defined by prescription M1.

Obligations are numbered **O-1, O-2, …**. Each is something the project must
**prove** (or, where marked, **define** after author approval). None may be
added as a hypothesis of a source-facing theorem. Where the source skips or
misprints a step, the [findings ledger](campaign/FINDINGS.md) says so.

## Target

$$[r]\,F_2(0;r)=\tfrac12,\qquad r=\alpha/\pi,$$

where $F_2$ is the Pauli form factor of the on-shell renormalized vertex
function (63.18), and $[r]$ extracts the coefficient of $r$. The result is to
hold in the limit of regulator removal. It must come with the magnetic
interpretation $g=2[F_1(0)+F_2(0)]$ and $F_1(0)=1$, which give $a_e=F_2(0)$, so
that $a_e^{(1)}=\alpha/2\pi$ ((63.22), (64.17)).

## Stage 0 — Model data

These are definitions. Each is meaning-carrying and needs author approval of
its exact Lean form.

| Datum | Source | Project choice |
| --- | --- | --- |
| Fields, Lagrangian, gauge symmetry | (58.1)–(58.16), pp. 345–347 | as source |
| Counterterm Lagrangian $Z_1,Z_2,Z_3,Z_m$ | (62.2)–(62.3), p. 369 | as source; the finite parts are fixed by the on-shell conditions below |
| Propagators and vertex | rule 9, p. 349; free electron propagator after (62.12), p. 371; (62.29) | photon propagator regulated as in [REGULARIZATION.md, section 3](REGULARIZATION.md#3-the-regulated-model-ingredients) |
| Loop integral | (62.40); chapter 14 | prescription M1 ([REGULARIZATION.md, section 4](REGULARIZATION.md#4-what-the-minkowski-loop-integral-means)) |
| Renormalization conditions | (62.11), (62.27), (63.1) | as source |
| Observable | (64.4)–(64.7) | both the source definition and the vertex-response definition, proved equivalent (author ruling D-9) |

**Where the formal model starts (author ruling D-8: option 2).** The source
derives its Feynman rules from a fermionic path integral, (58.17)–(58.21). A
Lean development cannot use an oscillatory infinite-dimensional path integral
as an ordinary integral ([WHAT-IS-PROVED.md, section 2](WHAT-IS-PROVED.md#2-what-must-be-specified-about-the-model)).
The candidate starting points are:

1. **Feynman rules as the definition.** Momentum-space rule 9, LSZ, and the
   diagram sum are taken as the model. The combinatorial derivation from the
   interaction is not formalized. This is the smallest option, but stage 1
   then becomes a modeling statement rather than a theorem.
2. **Formal interaction expansion, momentum space** (approved, D-8). The order-$e^3$
   amputated electron–electron–photon function is defined as the finite sum
   over Wick contractions of three interaction vertices (or two plus the
   external field), with fermionic signs, using the momentum-space free
   propagators. Stage 1 is then a finite combinatorial theorem. It needs new
   Wick/Grassmann-sign infrastructure; Mathlib has `Equiv.Perm.sign` and
   `ExteriorAlgebra` but no Wick theorem
   ([inventory, section 8](MATHLIB-INVENTORY.md#8-fermionic-and-combinatorial-structures)).
3. **Position-space time-ordered products.** This needs products of
   distributions and their Fourier transforms. It is out of scope for the
   pilot.

The choice determines what "derived from the interaction" means in the headline
theorem, so it was put to the author. On 2026-11-07 the author approved option 2
(D-8). Stage 1 is therefore a finite combinatorial theorem about the Wick
expansion, and the Wick and Grassmann-sign infrastructure is in scope.

## Stage 1 — From the interaction to the vertex function

Source: the path integral (58.17)–(58.21); Feynman rules, pp. 348–350; LSZ for
spinors (41.17)–(41.29) and photons (56.1)–(56.8); the worked LSZ-to-rules
example (45.11)–(45.16); the vertex function (62.39); the exact amplitude in
Fig. 63.1, p. 379.

The vertex function $iV^\mu(p',p)$ is the sum of 1PI diagrams with incoming
electron $p$, outgoing electron $p'$, and incoming photon $q=p'-p$ (62.39):
$$iV^\mu(p',p)=iZ_1e\gamma^\mu+iV^\mu_{1\,\mathrm{loop}}(p',p)+O(e^5).$$

The target object is $V^\mu$ itself, as in the source: $F_2$ is defined from it
by (63.18). Leg corrections are not part of $V^\mu$; they enter the on-shell
amplitude (Fig. 63.1).

- **O-1 (diagram content of $V^\mu$).** At order $e^3$, the 1PI
  electron–electron–photon function consists of exactly two pieces: the
  counterterm-corrected tree vertex $iZ_1e\gamma^\mu$, and the one-loop diagram
  of Fig. 62.3. Under D-8 this is a theorem about the 1PI part of the
  Wick expansion. It also needs the statements that tadpoles vanish (Furry's
  theorem, problem 58.2) and that disconnected and vacuum terms cancel by the
  normalization $Z(0,0,0)=1$ (58.21).
- **O-2 (coefficient and sign of the loop).** The 1PI diagram equals
  $$iV^\mu_{1\,\mathrm{loop}}=(ie)^3\bigl(\tfrac1i\bigr)^3\int_M\frac{d^4\ell}{(2\pi)^4}\bigl[\gamma^\rho\tilde S(\not p'+\not\ell)\gamma^\mu\tilde S(\not p+\not\ell)\gamma^\nu\bigr]\tilde\Delta_{\nu\rho}(\ell)
  \qquad\text{(62.40)}$$
  with coefficient one. This includes the fermion-line ordering and the
  absence of a closed-loop sign.
- **O-3 (amplitude, amputation, and residues).** Fix the amputation convention:
  the full external propagators are removed, and each external line keeps the
  LSZ residue factor. Then the order-$e^3$ on-shell amplitude equals
  (electron residue factors) $\times\ \bar u_{s'}(p')V^\mu u_s(p)\ \times$
  (photon-leg factor). The conditions $\Sigma(-m)=\Sigma'(-m)=0$ ((62.27),
  (62.36)–(62.38)) make the electron residue factors equal to $1$, which is the
  "unit residue" of the Fig. 63.1 caption. The photon-leg factor is fixed by
  $\Pi(0)=0$ (62.11). It is not needed for $F_2$, but it enters the magnetic
  interpretation (stage 5).

## Stage 2 — The regulated loop integral

Denominators: $A_1=(p+\ell)^2+m^2-i\epsilon$, $A_2=(p'+\ell)^2+m^2-i\epsilon$,
and $A_3^{(M)}=\ell^2+M^2-i\epsilon$ for $M\in\{m_\gamma,\Lambda\}$. The
Pauli–Villars photon is the difference of the $M=m_\gamma$ and $M=\Lambda$
terms. Each term below carries a subscript $M$, and only the difference is
integrated in the outer integral.

- **O-4 (four-dimensional numerator).** With the numerator of (62.45),
  $N^\mu=\gamma_\nu(-\not p'-\not\ell+m)\gamma^\mu(-\not p-\not\ell+m)\gamma^\nu$,
  and the shift $\tilde\ell=\ell+x_1p+x_2p'$ (62.43):
  $$N^\mu=\gamma_\nu\not{\tilde\ell}\gamma^\mu\not{\tilde\ell}\gamma^\nu+\tilde N^\mu+(\text{terms linear in }\tilde\ell),$$
  with $\tilde N^\mu$ as in (62.46). In four dimensions, after symmetric
  integration, $\gamma_\nu\not{\tilde\ell}\gamma^\mu\not{\tilde\ell}\gamma^\nu\to\tilde\ell^2\gamma^\mu$.
  This is (62.47)–(62.48) at $d=4$, where $(d-2)^2/d=1$, using
  $\gamma_\rho\gamma^\mu\gamma^\rho=2\gamma^\mu$ (47.18)–(47.21).
  Also $\tilde N^\mu=2\not a_2\gamma^\mu\not a_1+4m(a_1+a_2)^\mu+2m^2\gamma^\mu$
  with $a_1,a_2$ from (63.9); this is (63.10), whose contraction identities are
  left to problem 47.2.
- **O-5 (Feynman parameters).** For $A_1,A_2,A_3$ with negative imaginary part,
  $$\frac{1}{A_1A_2A_3}=\int dF_3\,\frac{1}{(x_1A_1+x_2A_2+x_3A_3)^3},\qquad
  x_1A_1+x_2A_2+x_3A_3=\tilde\ell^2+D_M-i\epsilon,$$
  with $\int dF_3$ as in (62.42) and $D_M$ as in (62.44), with $m_\gamma\to M$.
  The source states the formula as (14.9)–(14.11) and leaves its proof to
  problem 14.1. K(8)–K(15), pp. 2–4, display the parametrization and the
  shift.
- **O-6 (prescription M1, inner steps).** For fixed $\vec\ell$ and $\epsilon>0$:
  - the energy integral converges absolutely;
  - Fubini holds on (simplex) $\times\ \mathbb R_{\ell^0}$;
  - the real energy shift is valid.
- **O-7 (energy integrals; the Wick rotation).** For $w\in\mathbb C\setminus[0,\infty)$:
  $$\int_{\mathbb R}\frac{dt}{(-t^2+w)^3}=-\frac{3\pi}{8}(-w)^{-5/2},\qquad
  \int_{\mathbb R}\frac{t^2\,dt}{(-t^2+w)^3}=-\frac{\pi}{8}(-w)^{-3/2},$$
  with principal branches. The proof is by holomorphy in $w$ and the identity
  theorem, starting from $w<0$. This replaces the informal contour argument
  (14.16) and the explicit rotation K(40). **Proved in Lean** (2026-11-08) as
  `QED.Integration.integral_neg_sq_add_zpow_three` and
  `integral_sq_mul_neg_sq_add_zpow_three` (`QED/Integration/EnergyIntegral.lean`),
  under the hypothesis $-w\in$ slit plane, which is equivalent to
  $w\notin[0,\infty)$. This is infrastructure, not a source-facing result.
- **O-9 (outer steps).**
  - The energy-integrated, Pauli–Villars-paired function is jointly integrable
    on (simplex) $\times\ \mathbb R^3$.
  - Fubini moves $\int dF_3$ outside, and the spatial shift is valid.
  - Terms odd in $\tilde\ell$ vanish. The source asserts this ("integrate to
    zero", p. 376).
  - The tensor terms $\tilde\ell^\mu\tilde\ell^\nu$ reduce to $g^{\mu\nu}\tilde\ell^2/4$.
    The source (62.18) and K(28)–K(29) both state the $d$-dimensional version,
    which gives this at $d=4$. Because M1 splits energy and space, the reduction
    is a statement about the iterated integrals of Pauli–Villars pairs, proved
    in the limit $\epsilon\to0^+$.
- **O-10 ($\epsilon\to0^+$).** All limits exist by dominated convergence, using
  $D_M\ge m^2M^2/(m^2+M^2)>0$ for on-shell $p,p'$ and $q^2\ge0$
  ([REGULARIZATION.md, section 5](REGULARIZATION.md#5-renormalization-conditions-gauge-and-order-of-limits)).
- **O-11 (closed forms).** As $\epsilon\to0^+$,
  $$\int_M\frac{d^4\tilde\ell}{(2\pi)^4}\frac{1}{(\tilde\ell^2+D-i\epsilon)^3}=\frac{i}{32\pi^2D},\qquad
  \int_M\frac{d^4\tilde\ell}{(2\pi)^4}\left[\frac{\tilde\ell^2}{(\tilde\ell^2+D_{m_\gamma})^3}-\frac{\tilde\ell^2}{(\tilde\ell^2+D_\Lambda)^3}\right]=\frac{i}{16\pi^2}\ln\frac{D_\Lambda}{D_{m_\gamma}}.$$
  The first combines the Wick-rotation factor of (14.16) with the Euclidean
  master integral (14.27) at $d=4$. The second is the finite Pauli–Villars
  counterpart of the pole in (62.49).

**Result of stage 2** (to be proved):
$$V^\mu_{1\,\mathrm{loop}}(p',p)=\frac{e^3}{16\pi^2}\int dF_3\left[\ln\frac{D_\Lambda}{D_{m_\gamma}}\,\gamma^\mu+\frac{\tilde N^\mu}{2D_{m_\gamma}}-\frac{\tilde N^\mu}{2D_\Lambda}\right].$$
Compare (62.49), which has the same $\tilde N^\mu/(2D)$ term and the
dimensional pole in place of the logarithm.

## Stage 3 — On-shell reduction and form factors

Set $p^2=p'^2=-m^2$ and sandwich between $\bar u_{s'}(p')$ and $u_s(p)$.

- **O-12 (on-shell numerator).** Moving every $\not p$ right (where
  $\not p u=-mu$) and every $\not p'$ left gives (63.13). With
  $p\cdot p'=-\tfrac12q^2-m^2$ this becomes (63.14):
  $$\tilde N^\mu\to2\bigl[(1-2x_3-x_3^2)m^2-(x_3+x_1x_2)q^2\bigr]\gamma^\mu-2m(x_3-x_3^2)(p'+p)^\mu-2m\bigl[(x_1+x_1^2)-(x_2+x_2^2)\bigr]\,(p'-p)^\mu .$$
  The source states (63.13) without displaying the computation. The
  $\gamma^\mu$ coefficient agrees with an independent derivation and with the
  numerical sanity script after translation (CONVENTIONS.md, section 7).
- **O-13 (symmetry).** On shell, $D_M=x_1x_2q^2+(1-x_3)^2m^2+x_3M^2$ (63.15).
  This is symmetric under $x_1\leftrightarrow x_2$, so the $(p'-p)^\mu$ term
  integrates to zero (p. 381).
- **O-14 (Gordon identity).**
  $\bar u'(p'+p)^\mu u=\bar u'[2m\gamma^\mu+2iS^{\mu\nu}q_\nu]u$ ((63.16), from
  (38.18)). The source's derivation is sketched, with details left to problem
  38.4. It gives (63.17).
- **O-15 (well-definedness of the form factors).** For on-shell $p\neq p'$ with
  $q^2>0$, the pair $(F_1,F_2)$ in
  $$\bar u_{s'}(p')V^\mu u_s(p)=e\,\bar u_{s'}(p')\bigl[F_1\gamma^\mu-\tfrac{i}{m}F_2S^{\mu\nu}q_\nu\bigr]u_s(p)\qquad\text{for all }\mu,s,s'\qquad\text{(63.18)}$$
  **exists and is unique**. Uniqueness is the linear independence of the two
  on-shell bilinears when $q\neq0$. Existence comes from stages 2–3, not from
  the general argument of problem 63.1, which the source leaves as an exercise.
  Since (63.18) defines $F_1,F_2$ by a characterization, the
  [freezing rules](ORCHESTRATOR-LAUNCH.md#exact-declarations-and-the-approval-gate)
  require this existence-and-uniqueness theorem before the form factors can be
  defined.
- **O-8 (the counterterm feeds only $F_1$).** The counterterm
  $(Z_1-1)e\gamma^\mu$, the only other order-$e^3$ piece of $V^\mu$ (O-1), is a
  multiple of $\gamma^\mu$. It therefore contributes to $F_1$ alone
  ([REGULARIZATION.md, section 1](REGULARIZATION.md#1-what-has-to-be-regulated-at-order-e2)).
  The leg factors of O-3 are not part of $V^\mu$.
- **O-16 (the regulated Pauli form factor).** From stages 2–3:
  $$F_2(q^2;m_\gamma,\Lambda)=\frac{e^2}{8\pi^2}\int dF_3\,(x_3-x_3^2)\left[\frac{1}{x_1x_2q^2/m^2+(1-x_3)^2+x_3m_\gamma^2/m^2}-\frac{1}{x_1x_2q^2/m^2+(1-x_3)^2+x_3\Lambda^2/m^2}\right]+O(e^4).$$
  The first term at $m_\gamma=0$ is (63.20). The source sets $m_\gamma=0$
  there (p. 382). The project keeps $m_\gamma>0$ until the final limit.
- **O-17 (charge condition).** The condition (63.1)–(63.2) determines the finite
  part of $Z_1$ (the analogue of $\kappa_1$ in (63.7)), giving $F_1(0)=1$
  exactly (64.2). With route B, the pole of $Z_1$ (62.50) becomes a logarithm of
  $\Lambda$, and the infrared logarithm in $\kappa_1$ (63.12) is regulated by
  $m_\gamma$. The Ward identity
  $Z_1=Z_2$ (68.13) is not needed for $F_2$. It is a separate check of the
  charge interpretation.

## Stage 4 — Limits and the coefficient

- **O-18 ($q^2\to0^+$).** $F_2(q^2;m_\gamma,\Lambda)\to F_2(0;m_\gamma,\Lambda)$,
  by dominated convergence using positivity of $D_M$.
- **O-19 (regulator removal).** With $e^2/8\pi^2=r/2$ and
  $\int dF_3\,g(x_3)=2\int_0^1(1-x_3)g(x_3)\,dx_3$:
  $$F_2(0;m_\gamma,\Lambda)=r\,C_1(m_\gamma,\Lambda)+O(r^2),\qquad C_1(m_\gamma,\Lambda)\to\tfrac12\ \text{as}\ (m_\gamma,\Lambda)\to(0,\infty)\ \text{jointly}.$$
  The bounds and numerical values are in
  [REGULARIZATION.md, section 6](REGULARIZATION.md#6-regulator-dependence-of-the-target-and-bounded-feasibility).
  For $q^2>0$ the source's one-variable form (63.21) has the wrong sign in its
  denominator (F-6). The coefficient at $q^2=0$ is unaffected.
- **O-20 (perturbative bookkeeping).** The coefficient $[r]F_2(0)$ must be a
  defined object that does not presuppose its value. The plan is order-by-order
  coefficient functions: the $e^1$ and $e^3$ coefficients of $V^\mu$, and the
  $e^2$ coefficient of $F_2$. Packaging these as a truncated power series
  (`PowerSeries.trunc`) is optional. A formal series cannot stand in for an
  analytic remainder bound ([WHAT-IS-PROVED.md, section 4](WHAT-IS-PROVED.md#4-perturbation-theory-can-be-exact-mathematics)).

## Stage 5 — Magnetic interpretation

Source: chapter 64, pp. 383–385. The source argues as follows:

1. The vertex at $q^2\to0$ "follows from a quantum action" (64.3). This is
   asserted.
2. An interaction Hamiltonian $H_1$ for a constant field
   $A=(0,Bx,0)$ is defined from that action (64.6).
3. The magnetic moment is defined by $\mu B\equiv-\langle e|H_1|e\rangle$ for a
   rotationally invariant wave packet at rest with spin up (64.4)–(64.7).
4. The evaluation (64.8)–(64.15) gives $\langle e|H_1|e\rangle=-\frac{eB}{2m}\bigl(1+\frac{\alpha}{2\pi}\bigr)$.
5. Hence $g=2(1+\alpha/2\pi)$ (64.16)–(64.17).

The passage from the vertex function to (64.3) and (64.6) is a modeling step
that the source does not prove (F-8).

- **O-21 (vertex to magnetic coupling).** Prove that the linear-in-$B$ energy of
  the source's rest-frame, spin-up wave packet in the constant field is
  determined by the vertex function at $q\to0$, and that it equals
  $-\frac{eB}{2m}[F_1(0)+F_2(0)]$. This must be derived from $V^\mu$ directly,
  without assuming the quantum action (64.3). The field's normalization uses
  the photon-leg condition $\Pi(0)=0$. Route B does not regulate $\Pi$, so if
  this step needs $\Pi$ explicitly, its regulator must be specified here.
- **O-22 (Breit-frame structure).** For on-shell momenta in the Breit frame
  $p=(E,-\vec q/2)$, $p'=(E,\vec q/2)$, the spatial components of the bracket in
  (63.18), sandwiched between spinors, equal an exact multiple of
  $\epsilon^{ijk}q^j\,\xi'^\dagger\sigma^k\xi\,(F_1+F_2)$, the magnetic Sachs form
  factor. A numerical check in the mostly-minus convention is check 8 of the
  sanity script. It is the core of the response definition below, and a
  route to O-21.
- **O-23 (conclusion).** $g=2[F_1(0)+F_2(0)]$, with $F_1(0)=1$, gives
  $a_e=(g-2)/2=F_2(0)=\alpha/2\pi+O(\alpha^2)$.

**Observable definitions (author ruling D-9: both, proved equivalent).**

- **Source definition.** This follows (64.4)–(64.7): $\mu B\equiv-\langle e|H_1|e\rangle$
  for a normalized, rotationally invariant one-electron wave packet at rest
  with spin up, in the limit of sharply peaked packets. Here $H_1$ is the
  linear-in-$B$ interaction with the constant field $A=(0,Bx,0)$. To avoid
  circularity (F-8), the one-electron matrix elements of $H_1$ must come from
  the model's current matrix elements via O-3. The source instead inserts the
  values $F_1(0)$ and $F_2(0)$ in (64.6), and the project may not. This
  definition needs one-particle states with the normalization (41.5), wave
  packets, and an explicit limit of sharply peaked packets; see candidate
  finding F-11 on the source's width condition.
- **Response definition.** $\mu$ is read off from the spin-dependent,
  linear-in-$q$ part of the static-field matrix element of the vertex
  function (O-22). By O-22 it equals $\frac{e}{2m}G_M(0)$ with $G_M=F_1+F_2$.
  Its magnetic-moment meaning on its own would rest on matching to the Born
  amplitude of a nonrelativistic spin, as in `liu-mit-8324-l15` (3)–(11). That
  matching is a modeling identification, not a theorem; the equivalence
  theorem below is what ties this definition to the source's.
- **O-24 (equivalence).** The two definitions give the same $\mu$, at the
  perturbative order computed and in the stated limits: the sharply peaked
  packet, $\epsilon\to0^+$, and the regulator limits, in an order to be fixed
  with the exact declarations. With O-21 and O-22 this gives
  $\mu=\frac{e}{2m}[F_1(0)+F_2(0)]$ for both definitions, and with
  $F_1(0)=1$ it gives $g=2[1+F_2(0)]$.

Defining $g$ outright as $2[F_1(0)+F_2(0)]$ would name a scalar after the
observable, which the [outline](PROJECT-OUTLINE.md#3-first-complete-theorem)
rules out, so the project does not do it. Both definitions above define $\mu$
from a response computed in the model. Their relation to $F_1+F_2$ is proved
(O-21, O-22, O-24), not assumed.

## Toward exact declarations

No exact declaration is ready for approval. Every source-facing statement needs
carriers that do not yet exist in Lean. Stated honestly, the next obstruction is
infrastructure, and the source-facing work it unblocks is:

| Needed carrier or definition | Kind | Status |
| --- | --- | --- |
| Minkowski vectors with the mostly-plus form; on-shell momenta | infrastructure definition | form proved (`QED/Algebra/Minkowski.lean`); on-shell momenta missing |
| Weyl gamma matrices with the Clifford relation (36.9), $S^{\mu\nu}$, Dirac adjoint | infrastructure, meaning-carrying | proved (`QED/Algebra/Dirac.lean`), with the contraction identities (47.18)–(47.21) at $d=4$ (`QED/Algebra/Contraction.lean`) |
| On-shell spinors $u_s(p)$, normalization (38.17), Gordon identity | infrastructure, meaning-carrying | proved for the closed-form spinors: Dirac equations (38.1) and (38.16), normalization (38.17), and Gordon (38.18) (`QED/Algebra/Gordon.lean`, `QED/Algebra/Spinor.lean`). Equality with the source's boost definition (38.12) is pending. |
| Regulated propagators; the Minkowski integral of prescription M1 with explicit integrability (no silent zero for non-integrable data) | source-facing definitions | design open; the energy-integral evaluation it relies on (O-7) is proved |
| Regulated one-loop vertex $V^\mu_{1\,\mathrm{loop}}(p',p;m_\gamma,\Lambda)$ (62.40) | source-facing literal definition | depends on the rows above |
| Wick expansion at order $e^3$ with fermionic signs, from momentum-space propagators (D-8) | source-facing definition; meaning-carrying | missing; needs Wick and Grassmann-sign infrastructure (inventory 8.4) |
| Renormalized order-$e^3$ vertex with the charge condition | source-facing definition | depends on the Wick expansion and O-17 |
| Existence and uniqueness of $(F_1,F_2)$ (O-15), then the form factors from it | theorem, then definition | depends on the rows above |
| Headline: $C_1(m_\gamma,\Lambda)\to\tfrac12$, with $C_1$ the $e^2$ coefficient of $F_2(0)$ | theorem | depends on all of the above |
| One-particle states (41.5), wave packets, and one-particle current matrix elements | infrastructure, meaning-carrying | missing; needed by the source definition of $\mu$ (D-9) |
| Source and response definitions of $\mu$; equivalence O-24; $g=2[1+F_2(0)]$ | definitions and theorems | depend on the rows above |

Lean's Bochner integral returns $0$ for non-integrable integrands, and
`limUnder` returns a junk value when the limit fails to exist. A source-facing
definition built on them would silently change meaning off its intended
domain. The exact declarations must therefore either restrict their carriers to
the parameter domain where integrability and the limits are proved (for
example $m_\gamma,\Lambda,\epsilon>0$ and $q^2\ge0$), or state results as
`Tendsto`/`HasSum`-style relations. Choosing between these is part of preparing
the review packet.

### Proposed anchor surface for the first review packets

This is a plan, not a set of declarations; nothing here can be approved as
written. It fixes the **order** in which exact declarations are prepared. The
freezing rules require an existence-and-uniqueness theorem to be proved before
any object the source defines by a characterization is introduced
([launch brief](ORCHESTRATOR-LAUNCH.md#exact-declarations-and-the-approval-gate)).
Three objects in the chain are of that kind:

- the Minkowski loop integral under M1, a limit as $\epsilon\to0^+$;
- the form factors (63.18), the unique coefficients of a decomposition;
- the finite part of $Z_1$, fixed by the condition (63.1).

**Packet 1: the regulated one-loop vertex.** Approved as written and frozen on
2026-11-08 (decision D-11). Steps 1a–1c are the frozen definitions (A)–(C), the
operation is (D), and 1d is the frozen theorem goal (E), which is `DRAFT_SORRY`.
Step 1e follows once (E) is proved and audited.

| Step | Declaration (planned) | Kind |
| --- | --- | --- |
| 1a | The regulated propagators: $\tilde S(\not p)=(-\not p+m)/(p^2+m^2-i\epsilon)$, and the Pauli–Villars photon factor $\frac{1}{k^2+m_\gamma^2-i\epsilon}-\frac{1}{k^2+\Lambda^2-i\epsilon}$ | literal definitions (source formulas with the D-5 regulator) |
| 1b | The integrand of (62.40), as a $4\times4$ complex matrix for each $\mu$, per unit $e^3$ | literal definition |
| 1c | The energy-first iterated integral over $\mathbb R\times\mathbb R^3$ | definition of a generic operation; used only inside statements that assert integrability |
| 1d | **Well-definedness (frozen theorem goal):** for $m>0$, $m_\gamma>0$, $\Lambda>0$, and on-shell positive-energy $p',p$, the inner and outer integrals are integrable for every $\epsilon>0$, and the iterated integral has a unique limit as $\epsilon\to0^+$. Here $q^2\ge0$ follows from the premises, so it is not assumed. | $\exists!$ theorem |
| 1e | After 1d is proved and audited: $V^\mu_{1\,\mathrm{loop}}(p',p;m_\gamma,\Lambda)$ as that limit, landed with its characterization theorem | definition and theorem |

**Packet 2: the Pauli form factor and the headline.**

| Step | Declaration (planned) | Kind |
| --- | --- | --- |
| 2a | **Decomposition (frozen theorem goal):** for on-shell $p\neq p'$ with $q^2>0$, there is a unique pair $(A,B)$ with $\bar u_{s'}(p')V^\mu_{1\,\mathrm{loop}}u_s(p)=\bar u_{s'}(p')[A\gamma^\mu-\tfrac{i}{m}BS^{\mu\nu}q_\nu]u_s(p)$ for all $\mu,s,s'$. This is O-15 for the loop. The counterterm only shifts $A$ (O-8), so $F_2$ is the $B$ of the loop. | $\exists!$ theorem |
| 2b | After 2a: $F_2^{(1)}(p',p;m_\gamma,\Lambda)$ as the coefficient of $e^2$, with its characterization | definition and theorem |
| 2c | **Headline (frozen theorem goal):** $F_2^{(1)}\to\frac{1}{8\pi^2}$ jointly as $q^2\to0^+$ over on-shell pairs, $m_\gamma\to0^+$, and $\Lambda\to\infty$. Since $r=e^2/4\pi^2$, this is $[r]F_2(0)=\tfrac12$. | theorem |

The joint limit avoids defining $F_2(0)$ as another limit object. It also
avoids presupposing that $F_2^{(1)}$ depends on $(p,p')$ only through $q^2$.
The joint limit holds by the dominated bound of
[REGULARIZATION.md, section 6](REGULARIZATION.md#6-regulator-dependence-of-the-target-and-bounded-feasibility).

**Later packets.**

- **Wick derivation (D-8):** a theorem that the 1PI order-$e^3$ part of the
  Wick expansion is exactly the vertex of packet 1, together with the
  counterterm (O-1, O-2).
- **Charge condition and $Z_1$:** an $\exists!$ theorem, then a definition (O-17).
- **Magnetic moment (D-9):** the source and response definitions, O-21, O-22,
  and the equivalence O-24.

**Carrier choices still to settle in the packet.**

- Parameters: $\epsilon$, $m_\gamma$, $\Lambda$, and $m$ are either positive-real
  subtypes or reals with hypotheses. Subtypes avoid off-source values in the
  literal definitions, where Lean's $x/0=0$ would apply.
- On-shell pairs as a subtype of $(\mathbb R^4)^2$.
- The filter for the joint limit in 2c.
- Matrix-valued integrals entrywise. `Matrix (Fin 4) (Fin 4) ℂ` has no default
  normed-space instance in Mathlib, and integrating entry by entry avoids
  choosing a matrix norm.

A transient feasibility probe (untracked and deleted, 2026-11-08) elaborated
these shapes against the current carriers: steps 1a–1c, and the statement form
of 1d with entrywise integrability and an $\exists!$ limit along
$\epsilon\to0^+$. The probe is not a candidate declaration. Its only role was
to confirm that the packet can be written with the existing infrastructure.

Each candidate command is elaborated in a transient file and reviewed
independently against (62.40), (63.18), and (63.20) before it is shown to the
author.
