# Conventions

[Campaign HQ](../README.md) · [Sources](SOURCES.md) ·
[Regularization](REGULARIZATION.md) · [One-loop derivation](ONE-LOOP-DERIVATION.md)

**Status (2026-11-07):** adopted for the one-loop pilot (decision D-7). These are
the conventions of the primary source, Srednicki's prepublication draft
(`srednicki-draft` in [SOURCES.md](SOURCES.md)). Equation numbers `(n.m)` and
page numbers refer to that pinned PDF. Where the project deviates from the
source, the deviation is marked **Project**. No Lean declaration implementing
these conventions has been approved or frozen.

## 1. Units, charge, and coupling

| Item | Convention | Source |
| --- | --- | --- |
| Units | $\hbar=c=1$, Heaviside–Lorentz | (58.1), p. 345 |
| Electron charge | $e=-0.302822$ (negative) is the charge of the electron, defined by the on-shell condition (63.1) | (58.1), p. 345; (63.1)–(63.2), pp. 378–379 |
| Fine-structure constant | $\alpha=e^2/4\pi$ | (58.1); (63.22), p. 382 |
| Expansion parameter | **Project:** $r=\alpha/\pi$, as in the [outline](PROJECT-OUTLINE.md) | — |
| Current | $j^\mu=e\,\bar\Psi\gamma^\mu\Psi$ | (58.1) |
| Lagrangian | $\mathcal L=-\tfrac14F^{\mu\nu}F_{\mu\nu}+i\bar\Psi\not\partial\Psi-m\bar\Psi\Psi+e\bar\Psi\gamma^\mu\Psi A_\mu$ | (58.2), p. 345 |
| Covariant derivative | $D_\mu=\partial_\mu-ieA_\mu$ | (58.7), p. 346 |
| Counterterms | $Z_1,Z_2,Z_3,Z_m$ as in (62.2)–(62.3) | p. 369 |

## 2. Spacetime and momenta

| Item | Convention | Source |
| --- | --- | --- |
| Metric | $g_{\mu\nu}=\mathrm{diag}(-1,+1,+1,+1)$ (mostly plus) | (2.4), p. 30 |
| Square | $p^2=g_{\mu\nu}p^\mu p^\nu=-(p^0)^2+|\vec p|^2$ | (2.2) |
| Mass shell | $p^2=-m^2$, $p^0>0$ | (38.1), p. 240; p. 378 |
| Momentum transfer | $q=p'-p$, the incoming photon momentum; spacelike means $q^2>0$ | (63.1), p. 378; (64.1) |
| Plane waves | $e^{ipx}$ with $px=-p^0t+\vec p\cdot\vec x$ | (58.19)–(58.20), p. 348 |
| Position-space propagators | $S(x-y)=\int\frac{d^4p}{(2\pi)^4}\frac{-\not p+m}{p^2+m^2-i\epsilon}e^{ip(x-y)}$; $\Delta_{\mu\nu}(x-y)=\int\frac{d^4k}{(2\pi)^4}\frac{g_{\mu\nu}}{k^2-i\epsilon}e^{ik(x-y)}$ (Feynman gauge) | (58.19)–(58.20) |
| One-particle states | $\langle p,s,q|p',s',q'\rangle=(2\pi)^32\omega\,\delta^3(\vec p-\vec p')\delta_{ss'}\delta_{qq'}$ | (41.5), p. 263 |

**Notation clash.** In (62.43) Srednicki writes $q=\ell+x_1p+x_2p'$ for the
shifted loop momentum. In chapters 63–64 he writes $q=p'-p$. The project uses
$q=p'-p$ throughout and writes $\tilde\ell=\ell+x_1p+x_2p'$ for the shifted loop
momentum.

## 3. Dirac algebra

| Item | Convention | Source |
| --- | --- | --- |
| Representation | Weyl: $\gamma^\mu=\begin{pmatrix}0&\sigma^\mu\\ \bar\sigma^\mu&0\end{pmatrix}$, $\sigma^\mu=(I,\vec\sigma)$, $\bar\sigma^\mu=(I,-\vec\sigma)$ | (36.7)–(36.8), p. 227 |
| Clifford relation | $\{\gamma^\mu,\gamma^\nu\}=-2g^{\mu\nu}$, so $(\gamma^0)^2=1$, $(\gamma^j)^2=-1$ | (36.9), p. 227 |
| Slash | $\not p=\gamma^\mu p_\mu$, hence $\not p\not p=-p^2$ | (36.9) |
| Dirac adjoint | $\bar\Psi=\Psi^\dagger\beta$ with $\beta=\begin{pmatrix}0&I\\ I&0\end{pmatrix}$, numerically equal to $\gamma^0$ | (38.5), (38.7)–(38.9), pp. 240–241 |
| Lorentz generators | $S^{\mu\nu}=\tfrac{i}{4}[\gamma^\mu,\gamma^\nu]$; boost $K^j=S^{j0}$ | (40.3), p. 254; (64.11), p. 384 |
| Contraction identities | $\gamma_\rho\gamma^\mu\gamma^\rho=2\gamma^\mu$ in four dimensions, etc. | (47.18)–(47.21), p. 297 |

**Project.** The pilot works in exactly four dimensions (route B,
[REGULARIZATION.md](REGULARIZATION.md)). The $d$-dimensional identities of
(62.47)–(62.48) are not used.

## 4. Spinors

| Item | Convention | Source |
| --- | --- | --- |
| Dirac equation | $(\not p+m)u_s(p)=0$, $\bar u_s(p)(\not p+m)=0$ | (38.1), (38.16), pp. 240–242 |
| Rest spinors | $u_+(0)=\sqrt m\,(1,0,1,0)^T$, $u_-(0)=\sqrt m\,(0,1,0,1)^T$ | (38.6), p. 240 |
| Boosted spinors | $u_s(p)=\exp(i\eta\,\hat p\cdot\vec K)\,u_s(0)$, rapidity $\eta=\sinh^{-1}(|\vec p|/m)$ | (38.12), p. 241; (64.11) |
| Normalization | $\bar u_{s'}(p)u_s(p)=2m\,\delta_{s's}$; $\bar u_{s'}(p)\gamma^\mu u_s(p)=2p^\mu\delta_{s's}$ | (38.17), (38.21), p. 242 |
| Gordon identity | $2m\,\bar u_{s'}(p')\gamma^\mu u_s(p)=\bar u_{s'}(p')\bigl[(p'+p)^\mu-2iS^{\mu\nu}(p'-p)_\nu\bigr]u_s(p)$ | (38.18), p. 242 |
| Spin | $S^{12}u_\pm(0)=\pm\tfrac12u_\pm(0)$ | p. 385 |

**Project.** The boost formula (38.12) and the closed form
$u_s(p)=(m-\not p)\,u_s(0)/\sqrt{2m(m+p^0)}$ should agree. Proving this is a
small lemma, to be done before either is used as a definition. The form
factors are defined for all spin labels, so no physical statement depends on
the spinor basis.

## 5. Feynman rules (Feynman gauge)

From rule 9, p. 349, and chapter 62:

| Factor | Value | Source |
| --- | --- | --- |
| Vertex | $ie\gamma^\mu$; with counterterm, $iZ_1e\gamma^\mu$ | rule 9, p. 349; (62.39), p. 375 |
| Internal electron | $\frac1i\tilde S(\not p)$, $\tilde S(\not p)=\frac{-\not p+m}{p^2+m^2-i\epsilon}$, the free propagator; formally $(\not p+m-i\epsilon)^{-1}$ | rule 9, p. 349; after (62.12), p. 371. (The exact propagator is (62.27), p. 373.) |
| Internal photon | $\frac1i\tilde\Delta_{\mu\nu}(k)$, $\tilde\Delta_{\mu\nu}(k)=\frac{g_{\mu\nu}}{k^2-i\epsilon}$ | rule 9; (62.5) with $\xi=1$, p. 369 |
| IR regulator | $\tilde\Delta_{\mu\nu}(k)=\frac{g_{\mu\nu}}{k^2+m_\gamma^2-i\epsilon}$ (fictitious photon mass) | (62.29), p. 374 |
| **Project UV regulator** | $\tilde\Delta_{\mu\nu}(k)=g_{\mu\nu}\Bigl[\frac{1}{k^2+m_\gamma^2-i\epsilon}-\frac{1}{k^2+\Lambda^2-i\epsilon}\Bigr]$, replacing the source's dimensional regularization (decision D-5) | — |
| External lines | $u_s(p)$ for an incoming electron, $\bar u_{s'}(p')$ for an outgoing electron, times the unit residue of the pole | rule 9; Fig. 63.1 caption, p. 379 |
| Loop | $\int\frac{d^4\ell}{(2\pi)^4}$; **Project:** defined by prescription M1 ([REGULARIZATION.md, section 4](REGULARIZATION.md#4-what-the-minkowski-loop-integral-means)) | (62.40), p. 376 |

## 6. Vertex function and form factors

| Item | Convention | Source |
| --- | --- | --- |
| Vertex function | $iV^\mu(p',p)$ is the sum of 1PI diagrams with incoming electron $p$, outgoing electron $p'$, incoming photon $q=p'-p$; $iV^\mu=iZ_1e\gamma^\mu+iV^\mu_{1\,\mathrm{loop}}+O(e^5)$ | (62.39), p. 375 |
| One-loop term | $iV^\mu_{1\,\mathrm{loop}}=(ie)^3\bigl(\tfrac1i\bigr)^3\int\frac{d^4\ell}{(2\pi)^4}\bigl[\gamma^\rho\tilde S(\not p'+\not\ell)\gamma^\mu\tilde S(\not p+\not\ell)\gamma^\nu\bigr]\tilde\Delta_{\nu\rho}(\ell)$ | (62.40), p. 376 |
| Feynman parameters | $x_1$ for the electron line carrying $p$, $x_2$ for the line carrying $p'$, $x_3$ for the photon; $\int dF_3=2\int_0^1dx_1dx_2dx_3\,\delta(x_1+x_2+x_3-1)$ | (62.41)–(62.44), p. 376 |
| Charge condition | $\bar u_{s'}(p')V^\mu u_s(p)=e\,\bar u_{s'}(p')\gamma^\mu u_s(p)$ at $p^2=p'^2=-m^2$, $q^2=0$ | (63.1)–(63.2), pp. 378–379 |
| Form factors | $\bar u_{s'}(p')V^\mu u_s(p)=e\,\bar u_{s'}(p')\bigl[F_1(q^2)\gamma^\mu-\tfrac{i}{m}F_2(q^2)S^{\mu\nu}q_\nu\bigr]u_s(p)$ | (63.18), p. 381; (64.1) |
| Magnetic moment | $\mu B\equiv-\langle e|H_1|e\rangle$ for an electron at rest with spin up along $\vec B$; $\mu=g\cdot\tfrac12\cdot\tfrac{e}{2m}$ | (64.7), (64.16), pp. 384–385 |

## 7. Dictionary to the mostly-minus convention

Peskin–Schroeder, the Kaplunovsky notes, and Aoyama–Hayakawa–Kinoshita–Nio use
$\eta=\mathrm{diag}(+1,-1,-1,-1)$. The project's numerical sanity script uses
this convention too, but in the Dirac representation
([`scripts/numerics/one_loop_sanity.py`](../scripts/numerics/one_loop_sanity.py)). With
$g=-\eta$ and the same contravariant components $p^\mu$:

| Quantity | Srednicki (mostly plus) | Mostly minus |
| --- | --- | --- |
| Square | $p^2_S$ | $p^2_M=-p^2_S$; on shell $p^2_M=m^2$ |
| Lower index | $p_\mu^S$ | $p_\mu^M=-p_\mu^S$ |
| Clifford relation | $\{\gamma^\mu,\gamma^\nu\}=-2g^{\mu\nu}$ | $\{\gamma^\mu,\gamma^\nu\}=2\eta^{\mu\nu}$ (the same matrices) |
| Slash | $\not p_S=\gamma^\mu p^S_\mu$ | $\not p_M=-\not p_S$; Dirac equation $(\not p_M-m)u=0$ |
| Magnetic term | $-\tfrac{i}{m}F_2S^{\mu\nu}q^S_\nu$ | $+\tfrac{i}{2m}F_2\sigma^{\mu\nu}q^M_\nu$, with $\sigma^{\mu\nu}=\tfrac i2[\gamma^\mu,\gamma^\nu]=2S^{\mu\nu}$ |
| Form-factor argument | $F_2^S(q^2_S)$ | $F_2^M(q^2_M)=F_2^S(-q^2_M)$ |
| Interaction | $+e\bar\Psi\gamma^\mu\Psi A^S_\mu$ | $-e\bar\psi\gamma^\mu\psi A^M_\mu$ (the same term, since $A_\mu^S=-A_\mu^M$) |

$F_2(0)$ is the same number in both conventions.
