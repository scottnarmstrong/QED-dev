# Regularization and renormalization route for the one-loop pilot

[Campaign HQ](../README.md) · [Project outline](PROJECT-OUTLINE.md) ·
[Sources](SOURCES.md) · [Conventions](CONVENTIONS.md) ·
[One-loop derivation](ONE-LOOP-DERIVATION.md) · [Decisions](campaign/DECISIONS.md)

**Status (2026-11-07):** route selected for the one-loop pilot (decision D-5 in
the [decision log](campaign/DECISIONS.md)). This document is a mathematical plan.
It is not a Lean declaration, and nothing below has been approved or frozen.
The exact Lean definitions that implement these choices carry meaning and need
the author's approval before freezing.

Notation follows [CONVENTIONS.md](CONVENTIONS.md), which uses the conventions of
the primary source (Srednicki's draft). The metric is $\mathrm{diag}(-1,+1,+1,+1)$
with on-shell condition $p^2=-m^2$, spacelike $q=p'-p$ has $q^2>0$, and the
electron charge is $e<0$ with $\alpha=e^2/4\pi$. Equation numbers $(n.m)$ refer
to that source.

## 1. What has to be regulated at order $e^2$

The target object is the vertex function $V^\mu$ of (62.39), the sum of 1PI
diagrams, and $F_2$ is defined from it by (63.18). Relative to the tree vertex,
$V^\mu$ has exactly two order-$e^2$ contributions: the counterterm
$(Z_1-1)e\gamma^\mu$ and the one-loop diagram $V^\mu_{1\,\mathrm{loop}}$
(62.40). The on-shell amplitude in which $V^\mu$ appears (Fig. 63.1) also
carries external-leg factors. These are **not** part of $V^\mu$:

| Piece | Part of $V^\mu$? | UV, unregulated | IR, on shell, $m_\gamma\to0$ | Spinor structures |
| --- | --- | --- | --- | --- |
| One-loop 1PI diagram (62.40) | yes | log divergent, in the $\gamma^\mu$ part only (62.49) | at $q^2=0$ its $\gamma^\mu$ part diverges (the integral defining $\kappa_1$, (63.12)) | $\gamma^\mu$, $(p'+p)^\mu$, $(p'-p)^\mu$ |
| Counterterm $(Z_1-1)e\gamma^\mu$ | yes | carries the pole (62.50) | absorbs the infrared logarithm through the charge condition ((63.7), (63.12)) | $\gamma^\mu$ only |
| External electron legs | no; LSZ residue factors | $Z_2$, $Z_m$ divergent (62.34)–(62.35) | $\Sigma'(-m)$ needs $m_\gamma$; $\kappa_2$ (62.38) | scalar factors, equal to $1$ by $\Sigma(-m)=\Sigma'(-m)=0$ |
| Photon leg | no; photon propagator and residue | $Z_3$ divergent (62.24) | finite | fixed by $\Pi(0)=0$ (62.11) |
| Tadpoles | — | vanish (Furry's theorem, problem 58.2) | — | — |

Only the 1PI diagram can produce the magnetic structure $S^{\mu\nu}q_\nu$; the
counterterm is a multiple of $\gamma^\mu$. This is why $F_2$ needs no
renormalization at one loop (**proof obligation O-8** of the
[derivation](ONE-LOOP-DERIVATION.md); it is not an assumption). Since $F_2$ is
defined from $V^\mu$, the target needs only $V^\mu$ to be regulated.

The external legs and the photon leg matter elsewhere. They fix the meaning of
the charge in (63.1), and they relate $V^\mu$ to the measured amplitude
(obligation O-3). The electron self-energy that fixes the leg conditions has
one photon propagator, so route B regulates it. Route B does not regulate the
vacuum polarization. That enters only through $\Pi(0)=0$, in the charge
interpretation and the normalization of an external field (stage 5 of the
derivation). If that step uses $\Pi$ explicitly, its regulator must be
specified there (obligation O-21).

The full vertex integral must exist before it can be projected, so a regulator
is needed even though $F_2(0)$ is UV and IR finite:

- Without a UV regulator the one-loop integral (62.40) does not exist. Only its
  $\gamma^\mu$ part diverges (62.49), but projection has to act on an existing
  object.
- Without an IR regulator the on-shell loop at $q^2=0$ does not exist. Its
  $\gamma^\mu$ part contains
  $\int_0^1dx_3\,(1-x_3)(1-4x_3+x_3^2)/(1-x_3)^2$, which diverges at $x_3\to1$
  (the integral of (63.12)). Projecting the integrand onto $F_2$ before
  integration would substitute a different object for the vertex function.

## 2. Routes compared

| Route | Mathematical objects required | Fidelity / gauge | Lean feasibility for the pilot | Reuse beyond one loop |
| --- | --- | --- | --- | --- |
| **A. Dimensional regularization** in the UV, photon mass in the IR (the primary source's route, pp. 371–376) | meromorphic continuation in $d$ of $\int d^d\ell\,(\ell^2+D)^{-s}$; a formal $d$-dimensional Dirac algebra with $\gamma_\rho\gamma^\mu\gamma^\rho=(d-2)\gamma^\mu$ (62.48), which has no finite-dimensional realization for non-integer $d$ | the source's route; manifestly gauge invariant | heavy: a formal Clifford algebra over $\mathbb Q(d)$ and continuation theory, all unnecessary for a UV-finite $F_2$ | high: the standard route at two loops and beyond |
| **B. Pauli–Villars photon + photon mass** (4D), on-shell scheme | ordinary 4D integrals; photon propagator $\frac{1}{k^2+m_\gamma^2-i\epsilon}-\frac{1}{k^2+\Lambda^2-i\epsilon}$; explicit Dirac matrices | Ward identity preserved (only the photon line is modified, and it couples to the conserved current); the photon-mass IR regulator is the source's own (62.29) | moderate: every object is a finite-dimensional integral or matrix | partial: the photon regulator does not regulate fermion loops, so two loops (vacuum-polarization insertions) need regulator fermions, dimensional regularization, or subtraction |
| **C. Integrand subtraction (BPHZ / $K$-operation)** with an absolutely convergent Minkowski prescription | Zimmermann's forest formula; subtraction operators on integrands; photon mass for the IR | the subtracted amplitude is related to the on-shell scheme by a finite renormalization | heavy setup; at one loop it has the same $F_2$ limit as route B | high; close to the numerical higher-loop architecture of `ahkn-2012` |
| D. Project the integrand onto $F_2$ first | a UV/IR-finite scalar integral | **rejected**: the projected integral is not shown to be the amplitude's form factor | trivial | none |

**Choice for the pilot: route B**, in Feynman gauge, with the source's on-shell
renormalization conditions. Reasons:

1. Every object is classical and finite-dimensional: $4\times4$ complex matrices,
   Lebesgue integrals over $\mathbb R$, $\mathbb R^3$, and the Feynman-parameter
   simplex, and ordinary limits. There is no integration in non-integer
   dimension and no formal Clifford algebra.
2. It regulates the whole target object $V^\mu$, since the 1PI loop has one
   photon propagator. It also regulates the electron self-energy that fixes the
   external-leg conditions. It does not regulate the vacuum polarization, which
   is not part of $V^\mu$ (section 1).
3. It preserves the Ward–Takahashi identity at this order, so $Z_1=Z_2$ can be
   proved rather than imposed. $F_2$ does not need it, but the charge condition
   (63.1) relies on it for the magnetic interpretation, which uses the physical
   charge (cf. (68.13)).
4. The regulator dependence of the target is explicit and elementary
   (section 6), so removing the regulator is a bounded analysis problem.

**Deviation from the primary source.** The source regulates the UV
dimensionally. Its $F_2$ formula (63.20) is obtained after $\varepsilon\to0$,
with $m_\gamma$ set to zero where that is harmless (p. 382). Route B instead
produces the $m_\gamma>0$ version of (63.20), which equals (63.20) at
$m_\gamma=0$, plus a Pauli–Villars term that vanishes as $\Lambda\to\infty$
(section 6). The source names Pauli–Villars regularization as an alternative
in its scalar example, (14.22), p. 114. It notes that this route is more
cumbersome there, but the final result is the same. The finite parts of $Z_1$, $Z_2$, $\kappa_1$, $\kappa_2$ differ
between the routes; $F_2$ does not. This is recorded as finding F-2 in the
[findings ledger](campaign/FINDINGS.md).

This choice is **for the one-loop pilot only**. The two-loop phase must re-open
the regulator decision, with routes A and C as the candidates. The pilot's
Dirac-algebra, Feynman-parameter, and loop-integration infrastructure should be
built so that it does not depend on route B where avoidable.

## 3. The regulated model ingredients

All quantities depend on the photon mass $m_\gamma>0$, the Pauli–Villars mass
$\Lambda>0$, and $\epsilon>0$. Taking $\Lambda>m_\gamma$ is a convention, not a
premise. At $\Lambda=m_\gamma$ the regulated photon propagator vanishes, and for
$\Lambda<m_\gamma$ it changes sign. The packet-1 review confirmed that
well-definedness needs only $m_\gamma,\Lambda>0$.

- Electron propagator: $\frac1i\tilde S(\not p)$ with
  $\tilde S(\not p)=\frac{-\not p+m}{p^2+m^2-i\epsilon}$ (rule 9; the free propagator stated after (62.12), p. 371).
- Regulated photon propagator in Feynman gauge: $\frac1i\tilde\Delta_{\nu\rho}(\ell)$
  with
  $$\tilde\Delta_{\nu\rho}(\ell)=g_{\nu\rho}\left[\frac{1}{\ell^2+m_\gamma^2-i\epsilon}-\frac{1}{\ell^2+\Lambda^2-i\epsilon}\right]
  =g_{\nu\rho}\,\frac{\Lambda^2-m_\gamma^2}{(\ell^2+m_\gamma^2-i\epsilon)(\ell^2+\Lambda^2-i\epsilon)}.$$
  The first term alone is the source's (62.29).
- Vertex $ie\gamma^\mu$. The loop measure $\int\frac{d^4\ell}{(2\pi)^4}$ is
  defined in section 4.

The first term alone is the Feynman-gauge propagator of a massive
(Stueckelberg) photon coupled to a conserved current. The Pauli–Villars term
has a wrong-sign residue: it is a regulator and has no particle
interpretation. The physical model is recovered only in the limit
$m_\gamma\to0$, $\Lambda\to\infty$ of section 5.

The primary source does not justify using Feynman gauge with a photon mass.
The secondary source keeps it with a caveat: "this is not completely
consistent, but the inconsistencies go away in the $m_\gamma\to0$ limit"
(`kaplunovsky-vertex`, p. 15). For $F_2$, the relevant fact is that, between
on-shell spinors, the gauge-dependent $k^\mu k^\nu$ part of the photon
propagator feeds only the $\gamma^\mu$ structure (`knecht-2003`, p. 11, for
the massless photon). Route B fixes $\xi=1$, so the pilot's statement does not
rely on that argument.

**Power counting.** With the regulated photon line, the one-loop vertex
integrand (62.40) behaves at large $\ell$, in Euclidean norm, like
$|\ell|^2\cdot|\ell|^{-4}\cdot|\ell|^{-4}$: numerator $\not\ell\gamma^\mu\not\ell$,
two electron propagators, and the Pauli–Villars difference. This is degree
$-6<-4$, so the vertex is UV convergent by Euclidean power counting. The
electron self-energy (62.28) likewise has degree $-5$.

## 4. What the Minkowski loop integral means

Textbook manipulations treat $\int d^4\ell$ over Minkowski momenta as an ordinary
integral. With the Feynman prescription it is **not** a Lebesgue integral over
$\mathbb R^4$, even at fixed $\epsilon>0$ and even for UV-convergent integrands.
Near the light-cone shell $\ell^0\approx\pm\sqrt{|\vec\ell|^2+D}$,

$$\int_{\mathbb R}\frac{d\ell^0}{\bigl|-(\ell^0)^2+|\vec\ell|^2+D-i\epsilon\bigr|^{n}}
\;\ge\;\frac{c_n}{|\vec\ell|\,\epsilon^{\,n-1}}\qquad(|\vec\ell|\ \text{large},\ c_n>0),$$

so $\int d^3\ell$ of it diverges for every $n\ge1$; see finding F-1 in the
[findings ledger](campaign/FINDINGS.md). Translation invariance, Fubini, and
contour rotation are therefore unavailable as stated. The source treats Wick
rotation informally (chapter 14, (14.16), p. 112). The model needs a definition.

**Prescription M1 (selected).** For an integrand $f_\epsilon(\ell^0,\vec\ell)$
that is rational in $\ell^0$ with no real poles,

$$\int_M d^4\ell\,f:=\lim_{\epsilon\to0^+}\int_{\mathbb R^3}d^3\ell\left(\int_{\mathbb R}d\ell^0\,f_\epsilon(\ell^0,\vec\ell)\right),$$

with the energy integral taken first. This makes explicit the order of
operations that textbooks use when they Wick-rotate $\ell^0$ at fixed
$\vec\ell$. For the regulated vertex with $m_\gamma>0$, on-shell external
momenta, and $q^2\ge0$ (the only case the pilot needs), the steps are:

1. For fixed $\vec\ell$ and $\epsilon>0$, the inner integrand decays like
   $|\ell^0|^{-4}$ or faster and has no real poles. The inner integral therefore
   converges absolutely.
2. Feynman parametrization (the source's (14.9)–(14.11), whose proof is left to
   problem 14.1) holds pointwise. Each denominator, divided by $-1$, has positive
   imaginary part, so every convex combination is nonzero. For fixed $\vec\ell$,
   the joint integral over the simplex and $\ell^0$ converges absolutely, which
   justifies Fubini in the inner pair.
3. The real energy shift $\ell^0\mapsto\tilde\ell^0=\ell^0+x_1p^0+x_2p'^0$ is
   legitimate in the inner integral. After the shift, the energy integrand at
   fixed $\vec\ell$ is a rational function of $t=\tilde\ell^0$ in
   $-t^2+w$, with $w=|\vec{\tilde\ell}|^2+D-i\epsilon$. Since
   $\operatorname{Re}w>0$ and $\operatorname{Im}w<0$, $w$ lies in
   $\mathbb C\setminus[0,\infty)$. The integrals of $(-t^2+w)^{-3}$ and
   $t^2(-t^2+w)^{-3}$ are evaluated on that slit domain by analytic
   continuation from $w<0$, where $-t^2+w<0$ has no real zeros. Both sides are
   holomorphic on the connected domain and agree on $(-\infty,0)$. This
   replaces the contour-rotation argument of (14.16) without any contour
   deformation.
4. The resulting function of the Feynman parameters and $\vec\ell$ is jointly
   integrable when the Pauli–Villars pair is kept together. Fubini then moves
   the simplex integral outside, and the spatial shift is an ordinary Lebesgue
   translation.
5. The $\epsilon\to0^+$ limit follows by dominated convergence, because
   $D\ge D_{\min}(m_\gamma)>0$ on the simplex (section 5).

Alternatives considered:

- **M2: Zimmermann's prescription**, with $i\epsilon(\vec\ell^{\,2}+m^2)$ in each
  denominator (W. Zimmermann, *Commun. Math. Phys.* 11 (1968) 1–8; not pinned).
  It makes UV-convergent Minkowski integrals absolutely convergent and is the
  classical rigorous BPHZ setting. It changes the integrand away from the
  Feynman form at finite $\epsilon$ and breaks covariance there, which
  complicates the shift and the tensor reduction. It is the recorded fallback,
  and the natural prescription for route C.
- **M3: Euclidean definition with analytic continuation** in the external
  momenta. Real Euclidean external momenta cannot be on shell, so this needs
  several-variable continuation of off-shell form factors to $p^2=-m^2$. That
  is more infrastructure than M1 for the same result.

Prescription M1 depends on a choice of time axis at finite $\epsilon$. The pilot
needs only the specific covariance statements it proves: the tensor reduction
$\tilde\ell^\mu\tilde\ell^\nu\to g^{\mu\nu}\tilde\ell^2/4$ in the limit (O-9),
and the existence half of (63.18) (O-15). General covariance of M1 is not
claimed; if later work needs it, it becomes a separate theorem.

## 5. Renormalization conditions, gauge, and order of limits

**Scheme.** The source's on-shell conditions:

- Electron propagator pole at $\not p=-m$ with unit residue:
  $\Sigma(-m)=\Sigma'(-m)=0$ ((62.27), p. 373; (62.36)–(62.38)). The external
  lines carry "the unit residue of the pole" (Fig. 63.1).
- Charge: $\bar u(p')V^\mu u(p)=e\,\bar u(p')\gamma^\mu u(p)$ on shell at $q^2=0$
  ((63.1)–(63.2)), hence $F_1(0)=1$ exactly ((64.2)). This fixes $Z_1$ through
  $\kappa_1$ (63.7).
- Photon: $\Pi(0)=0$ ((62.11), p. 370; (62.24)). At this order it affects only
  the $\gamma^\mu$ structure (section 1).

All counterterms enter as scalar multiples of tree structures. None contributes
to $F_2$ at order $e^2$ (obligation O-8).

**Gauge.** Feynman gauge, $\xi=1$ in (62.5), as in the source (62.29). Gauge
independence of $F_2(0)$ is not needed for the stated result; `knecht-2003`
(p. 11) gives an argument for it. It becomes a separate check if the model is
later stated for general $\xi$.

**Order of limits.**

1. $\epsilon\to0^+$ at fixed $m_\gamma,\Lambda$ (prescription M1).
2. On-shell external momenta $p^2=p'^2=-m^2$ with spacelike $q=p'-p$, $q^2>0$.
   The form factors $F_1(q^2;m_\gamma,\Lambda)$ and $F_2(q^2;m_\gamma,\Lambda)$ are
   defined by (63.18) for all spins. Uniqueness needs $q\neq0$, because
   $S^{\mu\nu}q_\nu$ vanishes at $q=0$.
3. $q^2\to0^+$, giving $F_2(0;m_\gamma,\Lambda)$. Equivalently, a trace
   projector at $q\to0$ (`knecht-2003`, (2.14)–(2.15); `ahkn-2012`, (4.4)) may be
   used. The two definitions must be shown to agree if both are used.
4. Regulator removal $(m_\gamma,\Lambda)\to(0,\infty)$. Section 6 shows that the
   joint limit exists for $F_2(0)$, so the target needs no iterated-limit
   convention. $F_1(0)=1$ holds identically by the charge condition.

**Positivity.** By (63.15), on shell
$D=x_1x_2q^2+(1-x_3)^2m^2+x_3m_\gamma^2$ on the simplex
$x_1+x_2+x_3=1$, $x_i\ge0$. For $q^2\ge0$ and $m_\gamma>0$,
$$D\ \ge\ (1-x_3)^2m^2+x_3m_\gamma^2\ \ge\ \frac{m^2m_\gamma^2}{m^2+m_\gamma^2}>0 .$$
The same holds with $m_\gamma$ replaced by $\Lambda$. Steps 1–3 therefore meet
no thresholds and no singularities.

## 6. Regulator dependence of the target and bounded feasibility

With these choices the reduction of (62.41)–(63.20), to be proved in the
[derivation](ONE-LOOP-DERIVATION.md), gives

$$F_2(q^2;m_\gamma,\Lambda)=\frac{e^2}{8\pi^2}\int dF_3\left[\frac{x_3-x_3^2}{x_1x_2q^2/m^2+(1-x_3)^2+x_3m_\gamma^2/m^2}-\frac{x_3-x_3^2}{x_1x_2q^2/m^2+(1-x_3)^2+x_3\Lambda^2/m^2}\right]+O(e^4).$$

The first term with $m_\gamma=0$ is (63.20). With $r=\alpha/\pi$, so that
$e^2/8\pi^2=r/2$, and with $\int dF_3\,g(x_3)=2\int_0^1dx_3\,(1-x_3)\,g(x_3)$:

$$F_2(0;m_\gamma,\Lambda)=r\,C_1(m_\gamma,\Lambda)+O(r^2),\qquad
C_1=\frac12\int_0^1dx_3\left[\frac{2x_3(1-x_3)^2}{(1-x_3)^2+x_3m_\gamma^2/m^2}-\frac{2x_3(1-x_3)^2}{(1-x_3)^2+x_3\Lambda^2/m^2}\right].$$

The first term increases to $\tfrac12$ as $m_\gamma\to0^+$. With
$a=m_\gamma^2/m^2$ and $u=1-x_3$, its deficit is
$a\int_0^1\frac{(1-u)^2}{u^2+a(1-u)}du$. Since
$\frac{(1-u)^2}{u^2+a(1-u)}\le\frac{1}{u^2+a}$ on $[0,1]$, the deficit lies in
$[0,\tfrac{\pi}{2}\tfrac{m_\gamma}{m}]$. Its leading behaviour is
$\tfrac{\pi}{2}\tfrac{m_\gamma}{m}+O\bigl((m_\gamma/m)^2\ln(m/m_\gamma)\bigr)$. The second lies in
$[0,\,m^2/(3\Lambda^2)]$, because its denominator is at least
$x_3\Lambda^2/m^2$. Hence $C_1\to\tfrac12$ jointly,
which is (63.22). Numerical sanity values (not proofs):
$C_1=0.38353,\ 0.48513,\ 0.49844,\ 0.49984$ at
$(m_\gamma/m,\Lambda/m)=(10^{-1},10),(10^{-2},10^2),(10^{-3},10^3),(10^{-4},10^4)$
([`scripts/numerics/one_loop_sanity.py`](../scripts/numerics/one_loop_sanity.py)).

**Feasibility.** Each step reduces to a bounded family of lemmas about
classical objects. The [Mathlib inventory](MATHLIB-INVENTORY.md) records the
available building blocks.

| Step | Lemma family | Main difficulty |
| --- | --- | --- |
| Dirac algebra | explicit Weyl-representation $4\times4$ complex matrices; Clifford relation (36.9); contraction identities (47.18)–(47.21); on-shell spinors and the Gordon identity (38.18) | bookkeeping; decidable by computation (`norm_matmul`) |
| Feynman parameters | $\frac{1}{ABC}=2\int_{\text{simplex}}\frac{1}{(x_1A+x_2B+x_3C)^3}$ for $A,B,C$ in an open half-plane whose boundary line passes through $0$ (here the lower half-plane) | simplex integral as iterated interval integrals; missing from Mathlib |
| Energy integral | holomorphy of $w\mapsto\int_{\mathbb R}(-t^2+w)^{-3}dt$ on $\mathbb C\setminus[0,\infty)$, the explicit value $-\tfrac{3\pi}{8}(-w)^{-5/2}$ for $w<0$, and the identity theorem | **proved** (`QED/Integration/EnergyIntegral.lean`, 2026-11-08) |
| Spatial integral | $\int_{\mathbb R^3}(|\vec\ell|^2+D)^{-5/2}d^3\ell=\frac{4\pi}{3D}$ and the Pauli–Villars-paired $\tilde\ell^2$ terms | radial integration in $\mathbb R^3$ (`integral_fun_norm_addHaar`) |
| Integrability and Fubini | uniform bounds on the inner integrals; joint integrability on simplex $\times\,\mathbb R^3$ | estimates near the light-cone shell at fixed $\epsilon$ |
| Limits | dominated convergence in $\epsilon$, $q^2$, $m_\gamma$, $\Lambda$ | uniform positivity of $D$ |
| Projection | uniqueness of the $(F_1,F_2)$ decomposition for $q\neq0$ on shell; Gordon identity; counterterm structures | linear independence of on-shell bilinears |

The route needs no non-classical mathematics. The largest items are the
light-cone estimates for Fubini at fixed $\epsilon$ and the derivation of the
one-loop integrand from the interaction (independent of the regulator; see the
[derivation](ONE-LOOP-DERIVATION.md), stage 1).
