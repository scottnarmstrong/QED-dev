# Errata and deviations

This record lists the places where the Lean statements and proofs of this
repository differ from the printed sources, and why. An **erratum** is an
error in a pinned source itself: a misprint, a wrong sign or index, or a
printed assertion that is false. Every erratum below was checked against the
pinned PDF, and each comes with a derivation from the source's own equations.
A **deviation** is a deliberate difference that is not an error of the source:
a different regulator, a definition of a step the source treats informally, a
reformulated or specialized statement, an explicit limit in place of an
approximation, or a different proof route. A step that the source omits or
argues informally counts as an erratum only when a printed assertion is false.
When the library supplies a missing argument for a true step, that is
described with the proof route. Counts refer to entries, not occurrences, and
editorial misprints are counted.

**Sources and locations.** The primary source is M. Srednicki, *Quantum Field
Theory*, the author's prepublication draft (616 pages, SHA-256
`7990bad06ed96750f742729bcc65292f169589739af29012bb110b70649b5621`). Its
equation numbers agree with the published edition (Cambridge University Press,
2007). Locations give the equation number and the page of the draft PDF, which
equals the printed draft page. In chapters 56–64 the published edition's page
numbers are 5 to 8 higher. The secondary source is the course notes "QED
Vertex Correction" (University of Texas at Austin, Fall 2012; no author is
printed, and the notes are attributed to V. Kaplunovsky from their URL;
SHA-256 `701e6894bfc50ba5ddfc051f12ae000f20a3283e5fb87e00110a4370ceeffa59`),
cited by equation number and PDF page. The PDFs are not redistributed; the
hashes identify the bytes that were checked.

**Effect on the main results.** No erratum changes a formal statement. Four
of them, at (63.6), the kinematics on p. 380, (63.21) and the wave-packet
width on p. 383, lie on the route from the vertex function to the magnetic
moment; in each case the formal statements agree with the corrected reading.

The headline theorem is `lszAmplitude_pauli_landeFactor_limit`. It starts
from the general Wick model, with Pauli–Villars regulator fermions, and from
the model's own LSZ amplitude of the electron current. For every $\eta\gt0$
there are $\delta\gt0$ and $R$ such that, whenever $m_\gamma\lt\delta$ and
$\Lambda\gt R$, counterterms exist that put the electron on shell and satisfy
the charge condition for that amplitude. For every such choice, the Pauli
form factor of the amplitude is within $\eta$ of $e^2/8\pi^2=\alpha/2\pi$ for
$0\lt q^2\lt\delta$, and both definitions of the magnetic moment give a Landé
factor within $\eta$ of $2(1+\alpha/2\pi)$, the source definition for every
sufficiently narrow packet. This holds for every value of $\delta_3$. The LSZ
results it is built from are
`lszAmplitude_existsUnique` and `lszAmplitude_eq` (the amplitude exists and is
the vertex function between spinors plus a photon-leg term),
`electronCounterterms_existsUnique` (the electron on-shell conditions fix
$\delta_2$ and $\delta_m$), `existsUnique_isLSZFormFactorPair` (the form
factors of the amplitude are well defined), and
`isLSZChargeNormalized_iff_isChargeNormalized`,
`isLSZResponseMagneticMoment_iff_isResponseMagneticMoment` and
`integrable_and_tendsto_lszSourceMagneticMoment` (the charge condition and
both magnetic-moment definitions, restated with the LSZ amplitude, are
equivalent to the original ones). These tie it to the theorems about the
vertex function, which remain main results:
`isFormFactorPair_vertexOneLoop_pauli_limit` ($F_2\to\alpha/2\pi$),
`isFormFactorPair_vertexFunction_dirac_limit` ($F_1\to1$),
`landeFactor_isResponseMagneticMoment_limit` and
`landeFactor_sourceMagneticMoment_limit` ($g\to2(1+\alpha/2\pi)$ for both
definitions of the magnetic moment), `integrable_and_tendsto_sourceMagneticMoment`
(the two definitions agree), and `QED.Wick.wickVertex_eq` and
`QED.Wick.tendsto_wickVertex` (the vertex function from the Wick expansion).
Each of these theorems depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

| Source | Errata | Deviations |
|---|---:|---:|
| Srednicki, *Quantum Field Theory* (draft) | 5 | 15 |
| "QED Vertex Correction" notes | 2 | 0 |
| Total | 7 | 15 |

## Srednicki, *Quantum Field Theory* (draft)

### Errata

1. **(56.6), p. 339.** Wrong sign (misprint). The photon normalization
   condition is printed $\langle k,\lambda|A^i(x)|0\rangle=\varepsilon^i_\lambda(\mathbf k)e^{ikx}$.
   Read $e^{-ikx}$. In the mode expansion (55.11),
   $\mathbf A(x)=\sum_\lambda\int\widetilde{dk}\ [\varepsilon^\ast_\lambda(\mathbf k)a_\lambda(\mathbf k)e^{ikx}+\varepsilon_\lambda(\mathbf k)a^\dagger_\lambda(\mathbf k)e^{-ikx}]$,
   only the creation term contributes to this matrix element, and it carries
   $e^{-ikx}$; (56.1)–(56.2) invert this same expansion. The author's errata
   list for the published edition has this entry (p. 344 there). No effect on
   the stated theorems: the photon LSZ formula is not formalized.

2. **(63.6), p. 379.** Missing sign (misprint). The second bracket of the
   numerator is printed $[-(1-x_1)\not p+x_2\not p'\ m]$. Read
   $[-(1-x_1)\not p+x_2\not p'+m]$. Equation (63.6) restates $\tilde N^\mu$ of
   (62.46), p. 376, as the text notes at the top of p. 380, and (62.46) has
   $+x_2\not p'+m$. The next step, (63.8)–(63.9), also writes this bracket as
   $\not a_2+m$ with $a_2=x_2p'-(1-x_1)p$. The author's errata list has this
   entry (p. 387 of the published edition). No effect on the stated theorems.
   The library does not use (63.6). It starts from the numerator of (62.40),
   in which both electron propagators carry $+m$, and proves the contraction
   (63.10) and the on-shell reduction (63.14), (63.17) from it; see
   `vertexNumeratorMatrix_eq` and `sandwich_vertexNumeratorMatrix_neg_shift`
   in [NumeratorReduction.lean](../QED/OneLoop/NumeratorReduction.lean).

3. **p. 380, last paragraph.** Wrong sign (misprint). The kinematics are
   printed "with $p^2=-p'^2=-m^2$". Read $p^2=p'^2=-m^2$: these are the mass
   shell conditions of the metric $\mathrm{diag}(-1,1,1,1)$, stated on p. 378
   and used in (63.15). The author's errata list has this entry (p. 388 of the
   published edition). No effect on the stated theorems, which assume
   $p^2=p'^2=-m^2$; see the hypotheses `hp` and `hp'` of
   `isFormFactorPair_vertexOneLoop_pauli_limit` in
   [PauliFormFactorLimit.lean](../QED/Frozen/OneLoop/PauliFormFactorLimit.lean).

4. **(63.21), p. 382.** Wrong sign (misprint). The denominator is printed
   $1-y(1-y)q^2/m^2$. Read
   $$F_2(q^2)=\frac{e^2}{8\pi^2}\int_0^1\frac{dy}{1+y(1-y)q^2/m^2}+O(e^4).$$
   The text derives (63.21) from (63.20) by integrating out $x_2$ and
   substituting $x_1=(1-x_3)y$. Then $x_1x_2=(1-x_3)^2y(1-y)$, the denominator
   of (63.20) becomes $(1-x_3)^2[1+y(1-y)q^2/m^2]$, and the remaining $x_3$
   integral equals 1. The printed form would also diverge for all spacelike
   $q^2\ge4m^2$, whereas the corrected form diverges only for timelike
   $q^2\le-4m^2$, at and beyond the pair-production threshold. At $q^2=0$ the two forms
   agree, so $F_2(0)=\alpha/2\pi$ in (63.22) is unaffected. The author's
   errata list has this entry (p. 389 of the published edition). No effect on
   the stated theorems. The library does not state (63.21). Its on-shell
   Pauli coefficient (`formFactorB_eq` in
   [PauliLimit.lean](../QED/OneLoop/PauliLimit.lean)) is built on the on-shell
   denominator $(1-y)M^2+y^2(m^2+x(1-x)q^2)$ of (63.15), written in Feynman
   parameters on the unit square (`feynmanMass_onShell` in
   [VertexFormFactors.lean](../QED/OneLoop/VertexFormFactors.lean)), with the
   plus sign. At $m_\gamma=0$ and without the regulator term its integrand is
   $2(1-y)/(1+x(1-x)q^2/m^2)$, whose $y$ integral is the corrected (63.21).
   This last integration is not a Lean theorem.

5. **p. 383, the condition after (64.5).** Reversed inequality (misprint). The
   wave packet $f(\mathbf p)\sim\exp(-a^2\mathbf p^2/2)$ is described as
   "sharply peaked at $\mathbf p=0$" and given the condition "with
   $a\ll1/m$". Read $a\gg1/m$. The momentum spread of this packet is of order
   $1/a$, and the evaluation relies on the sharp peak twice. First, (64.12)
   expands the boost (64.11) to linear order in $\mathbf p$, which requires
   the rapidity $\sinh^{-1}(|\mathbf p|/m)$ to be small on the packet. Second,
   (64.14) replaces $\int\widetilde{dp}\ |f(\mathbf p)|^2/2\omega$ by $1/2m$,
   using $\int\widetilde{dp}\ |f(\mathbf p)|^2=1$, which requires $\omega\approx m$
   on the packet. Both need $1/a\ll m$, that is, a packet larger than the
   Compton wavelength. Under the printed condition typical momenta are
   $|\mathbf p|\sim1/a\gg m$, so $\omega\approx|\mathbf p|$, the packet average
   of $1/2\omega$ is of order $a$ rather than $1/2m$, and (64.14)–(64.15) do
   not follow. No other reading rescues the printed condition: (64.5) and
   problem 64.1 both write the packet as $\exp(-a^2\mathbf p^2/2)$, so $a$ is a
   length; read as a momentum width, the comparison with $1/m$ would be
   dimensionally inconsistent. No entry for this page was found in the
   author's errata list.
   No effect on the stated theorems. The library's source definition uses
   packets $f(\mathbf k)=\varphi(|\mathbf k|^2/\lambda^2)$ with $\varphi$
   compactly supported, so the momentum support has radius of order $\lambda$,
   and it takes $\lambda\to0^+$; this is the corrected regime, with
   $a\sim1/\lambda\to\infty$. See `integrable_and_tendsto_sourceMagneticMoment`
   in [SourceMagneticMomentLimit.lean](../QED/Frozen/OneLoop/SourceMagneticMomentLimit.lean)
   and `landeFactor_sourceMagneticMoment_limit` in
   [SourceLandeFactorLimit.lean](../QED/Frozen/OneLoop/SourceLandeFactorLimit.lean).

### Deviations

| # | Location | Kind | Lean statement |
|---|---|---|---|
| 1 | (62.29), (62.47)–(62.50), pp. 371–377 | Pauli–Villars photon in four dimensions instead of dimensional regularization | `photonPropagator`, `vertexIntegrand` |
| 2 | p. 382, after (63.20) | Photon mass kept until the final limit | `isFormFactorPair_vertexOneLoop_pauli_limit` |
| 3 | (14.16), p. 112; (62.40) | Minkowski loop integral defined energy first | `energyFirstIntegral`, `vertexLimit_existsUnique` |
| 4 | (58.17)–(58.21), (62.39) | Model starts from the momentum-space Wick expansion | `wickVertex`, `wickVertex_eq`, `tendsto_wickVertex`, `onePIFunction`, `connectedFunction` |
| 5 | (62.39), (63.19)–(63.20), (64.17) | Vertex function truncated at order $e^3$ | `vertexFunction` |
| 6 | (63.18)–(63.22) | Form factors by characterization; $F_2(0)$ as a joint limit | `IsFormFactorPair`, `existsUnique_isFormFactorPair_vertexOneLoop`, `isFormFactorPair_vertexOneLoop_pauli_limit` |
| 7 | (63.1)–(63.3), (64.2) | Charge condition for all Dirac solutions; $F_1(0)=1$ at fixed regulators | `IsChargeNormalized`, `existsUnique_isChargeNormalized`, `isFormFactorPair_vertexFunction_dirac_limit` |
| 8 | (64.3)–(64.7), pp. 383–384 | Two magnetic-moment definitions, proved equivalent, in place of the asserted quantum action | `IsResponseMagneticMoment`, `sourceMagneticMoment`, `integrable_and_tendsto_sourceMagneticMoment` |
| 9 | (64.4)–(64.10) | Packet class, normalization and order of limits in the source definition | `packetCurrentDensity`, `packetNormSq`, `sourceMagneticMoment` |
| 10 | Fig. 63.1, (64.8) | Current matrix elements: the vertex function in the definitions, derived as the LSZ amplitude of the model | `lszAmplitude_eq`, `isLSZChargeNormalized_iff_isChargeNormalized`, `isLSZResponseMagneticMoment_iff_isResponseMagneticMoment`, `integrable_and_tendsto_lszSourceMagneticMoment` |
| 11 | (38.12), (63.1), (63.18) | Closed-form spinors; conditions stated for all Dirac solutions | `spinor`, `spinor_eq_exp_boost` |
| 12 | throughout | Lean conventions: domains, total functions, sign of $e$ | none |
| 13 | (62.12)–(62.25), pp. 371–372 | Pauli–Villars regulator fermions for the closed fermion loop | `Params`, `regulatedAmplitude`, `vacuumPolarization_existsUnique`, `photonCounterterm_existsUnique` |
| 14 | (64.3)–(64.7), pp. 383–384; (62.10)–(62.11) | External photon as a background field; $\Pi(0)=0$ not needed for $g$ | `lszAmplitude_existsUnique`, `lszAmplitude_eq`, `IsPhotonOnShell` |
| 15 | (41.17), (41.25), (62.27), (62.36)–(62.38) | On-shell conditions in covariant form; LSZ amplitude as an iterated limit | `selfEnergySlash`, `IsElectronOnShell`, `electronCounterterms_existsUnique`, `lszAmplitude` |

1. **pp. 371–377, (62.29) and (62.47)–(62.50): ultraviolet regulator.** The
   source continues to $d=4-\varepsilon$ dimensions for the ultraviolet and
   uses a photon mass for the infrared. The library works in exactly four
   dimensions and regulates the ultraviolet with a Pauli–Villars photon of
   mass $\Lambda$. The photon propagator is
   $$\tilde\Delta_{\nu\rho}(k)=g_{\nu\rho}\Bigl[\frac{1}{k^2+m_\gamma^2-i\epsilon}-\frac{1}{k^2+\Lambda^2-i\epsilon}\Bigr],$$
   whose first term is the source's (62.29); Feynman gauge is kept, as in the
   source. With this regulator the one-loop vertex is ultraviolet convergent,
   the $d$-dimensional identities (62.47)–(62.48) are replaced by their
   four-dimensional forms, and the pole in (62.49)–(62.50) becomes a logarithm
   of $\Lambda$. The finite part of $Z_1$ therefore differs from the source's
   (63.3), (63.7), (63.12). The Pauli form factor is the $m_\gamma\gt0$ form
   of (63.20) minus the same expression with $\Lambda$ in place of $m_\gamma$,
   and the second term vanishes as $\Lambda\to\infty$. Every statement takes
   $\Lambda\gt0$ and removes the regulator only at the end. The same
   propagator regulates the one-loop self-energy (62.28), with the
   Pauli–Villars logarithm in place of the pole of (62.33). The closed fermion
   loop of the vacuum polarization has no internal photon and needs a
   regulator of its own (Deviation 13). The source itself names Pauli–Villars
   regularization as an alternative after (14.22), p. 114. See
   `photonPropagator` in
   [PhotonPropagator.lean](../QED/Frozen/OneLoop/PhotonPropagator.lean) and
   `vertexIntegrand` in [VertexIntegrand.lean](../QED/Frozen/OneLoop/VertexIntegrand.lean).

2. **p. 382, after (63.20): photon mass.** The source sets $m_\gamma=0$ in
   $F_2$ and in the logarithm of $F_1$, since those terms are infrared finite.
   The library keeps $m_\gamma\gt0$ throughout and removes both regulators
   only in the final statements, jointly: $m_\gamma\to0^+$ and $\Lambda\to\infty$
   together. For $F_2$ and for both Landé factors the joint limit exists; for
   $F_1$ see Deviation 7. See `isFormFactorPair_vertexOneLoop_pauli_limit`,
   `landeFactor_isResponseMagneticMoment_limit` in
   [LandeFactorLimit.lean](../QED/Frozen/OneLoop/LandeFactorLimit.lean),
   `landeFactor_sourceMagneticMoment_limit`, and their LSZ form
   `lszAmplitude_pauli_landeFactor_limit` in
   [LszAmplitudePauliLandeFactorLimit.lean](../QED/Frozen/WickModel/LszAmplitudePauliLandeFactorLimit.lean).

3. **(14.16), p. 112, and (62.40): the Minkowski loop integral.** The source
   treats $\int d^4\ell$ over Minkowski momenta as an ordinary integral and
   rotates the energy contour informally. With the Feynman prescription the
   integrand is not Lebesgue integrable on $\mathbb R^4$, even at fixed
   $\epsilon\gt0$ and even when it converges by Euclidean power counting. For
   $D,\epsilon\gt0$, $n\ge1$ and $\omega^2=|\vec\ell|^2+D$, the region near
   $\ell^0=\pm\omega$ gives
   $$\int_{\mathbb R}\frac{d\ell^0}{\bigl|-(\ell^0)^2+\omega^2-i\epsilon\bigr|^n}\ \ge\ \frac{c_n}{\omega\epsilon^{n-1}}\qquad(|\vec\ell|\ \text{large}),$$
   and $\int d^3\ell/\omega=\infty$. Fubini's theorem, shifts and contour
   rotation are therefore not available as stated. The library defines the
   loop integral by the energy-first prescription: at fixed $\epsilon\gt0$,
   $\int d^3\ell\ \bigl(\int d\ell^0\ F\bigr)$ with the energy integral innermost,
   followed by the limit $\epsilon\to0^+$. The well-definedness theorem proves
   that both stages are integrable for every $\epsilon\gt0$ and that the limit
   exists and is unique. The energy integrals are evaluated by analytic
   continuation in place of the contour rotation (see the proof-route section
   below). See `energyFirstIntegral` in
   [EnergyFirstIntegral.lean](../QED/Frozen/OneLoop/EnergyFirstIntegral.lean),
   `vertexLimit_existsUnique` in
   [VertexLimitExists.lean](../QED/Frozen/OneLoop/VertexLimitExists.lean), and
   the one-loop vertex `vertexOneLoop` with its characterization
   `tendsto_energyFirstIntegral_iff_vertexOneLoop`
   ([VertexOneLoop.lean](../QED/Frozen/OneLoop/VertexOneLoop.lean),
   [VertexOneLoopSpec.lean](../QED/Frozen/OneLoop/VertexOneLoopSpec.lean)).

4. **(58.17)–(58.21), rules 1–12 and (62.39): starting point.** The source
   derives its Feynman rules from a fermionic path integral. The library starts
   from a finite object. At fixed $\epsilon\gt0$, $iV^\mu$ is defined as the
   sum of the one-particle-irreducible Wick contractions, with their fermionic
   signs, of the terms of $\exp(i\int\mathcal L_1)$ of total order at most
   $e^3$. The contractions use the momentum-space free propagators of the
   regulated model and the full counterterm Lagrangian (62.2)–(62.3), with
   free coefficients $\delta_1=Z_1-1$, $\delta_2$, $\delta_m$ and $\delta_3$.
   One-particle irreducibility is part of the definition, as in (62.39), so
   vacuum, disconnected and external-leg terms are excluded from the start;
   Furry's theorem and the normalization of the generating functional are not
   needed. The theorem shows that this sum equals $iZ_1e\gamma^\mu$ plus the
   one-loop diagram (62.40), with coefficient one, the fermion ordering
   $\gamma^\rho\tilde S\gamma^\mu\tilde S\gamma^\nu$ and no closed-loop sign, for
   all values of $\delta_2$, $\delta_m$, $\delta_3$. Its $\epsilon\to0^+$
   limit is the vertex function used in all the other statements. In this
   labelled expansion the two photon fields of the photon counterterm are
   distinguishable, so its vertex factor is half the rule (62.12), which counts
   both pairings. See `wickVertex` in
   [WickVertex.lean](../QED/Frozen/Wick/WickVertex.lean), `vertexFactor` in
   [VertexFactor.lean](../QED/Frozen/Wick/VertexFactor.lean), `wickVertex_eq`
   in [WickVertexEq.lean](../QED/Frozen/Wick/WickVertexEq.lean), and
   `tendsto_wickVertex` in
   [WickVertexLimit.lean](../QED/Frozen/Wick/WickVertexLimit.lean).

   The general model extends this expansion to any number of external
   electron and photon fields and adds the regulator fermions of Deviation 13.
   Its 1PI function sums the one-particle-irreducible contractions; its
   connected function sums the contractions whose external fields are
   attached and whose vertices are connected. The connected function
   therefore keeps the corrections on the external legs, while vacuum and
   disconnected terms are still excluded from the start. The vertex above is
   the 1PI function with one external fermion pair and one external photon,
   for all values of the regulator-fermion parameters, which do not enter it
   at this order. The self-energy (62.27)–(62.28) and the vacuum polarization
   (62.4), (62.12) are the 1PI functions of order $e^2$ with one external
   fermion pair and with two external photons. The current matrix element is
   obtained from the connected three-point function by the LSZ limit of
   Deviation 15. The path integral, position-space time-ordered products and
   the photon LSZ formulas of section 56 are not formalized. See
   `onePIFunction` in
   [OnePIFunction.lean](../QED/Frozen/WickModel/OnePIFunction.lean),
   `connectedFunction` in
   [ConnectedFunction.lean](../QED/Frozen/WickModel/ConnectedFunction.lean),
   and `wickVertex_eq_onePIFunction` in
   [WickVertexEqOnePIFunction.lean](../QED/Frozen/WickModel/WickVertexEqOnePIFunction.lean).

5. **(62.39), (63.19)–(63.20) and (64.17): truncation.** The source writes
   $V^\mu=Z_1e\gamma^\mu+V^\mu_{1\ \mathrm{loop}}+O(e^5)$ and states its results
   up to $O(e^4)$ and $O(\alpha^2)$. The library's vertex function is exactly
   $Z_1e\gamma^\mu+V^\mu_{1\ \mathrm{loop}}$, with $Z_1$ a real parameter that
   the charge condition then determines exactly. The limits are exact
   statements about this truncated function; for example
   $g\to2(1+e^2/8\pi^2)$, with no $O(\alpha^2)$ term. They give the coefficient of
   order $\alpha$ and say nothing about higher orders. The connected function
   and the LSZ amplitude are truncated in the same way, at order $e^3$. See
   `vertexFunction` in
   [VertexFunction.lean](../QED/Frozen/OneLoop/VertexFunction.lean).

6. **(63.18)–(63.22): form factors.** The source obtains $F_1$ and $F_2$ as
   the explicit integrals (63.19)–(63.20). The library defines a form-factor
   pair by the decomposition (63.18) itself, required for every $\mu$, every
   column $u$ with $(\not p+m)u=0$ and every row $\bar u'$ with
   $\bar u'(\not p'+m)=0$. It proves that for $e\ne0$, on-shell
   positive-energy momenta and $q^2\gt0$ such a pair exists and is unique; the
   existence comes from the explicit computation rather than from the general
   argument of problem 63.1. Uniqueness needs $q\ne0$, since
   $S^{\mu\nu}q_\nu$ vanishes at $q=0$. The value $F_2(0)$ is replaced by a
   joint limit: as $q^2\to0^+$ over on-shell positive-energy pairs,
   $m_\gamma\to0^+$ and $\Lambda\to\infty$, every form-factor pair of the
   one-loop vertex has second component within any $\eta\gt0$ of
   $e^2/8\pi^2=\alpha/2\pi$, uniformly in the momenta. This avoids defining
   $F_2(0)$ as a further limit object and does not presuppose that $F_2$
   depends on the momenta only through $q^2$. The form factors of the LSZ
   amplitude are defined in the same way, on the spinor bases (Deviation 11).
   For $e\ne0$ and $q^2\gt0$ the pair exists and is unique, and the headline
   theorem bounds its second component in the same joint limit; the
   photon-leg term of Deviation 14 changes only the first component. See
   `IsFormFactorPair` in
   [IsFormFactorPair.lean](../QED/Frozen/OneLoop/IsFormFactorPair.lean),
   `existsUnique_isFormFactorPair_vertexOneLoop` in
   [FormFactorExistsUnique.lean](../QED/Frozen/OneLoop/FormFactorExistsUnique.lean),
   `isFormFactorPair_vertexOneLoop_pauli_limit` in
   [PauliFormFactorLimit.lean](../QED/Frozen/OneLoop/PauliFormFactorLimit.lean),
   `IsLSZFormFactorPair` in
   [IsLSZFormFactorPair.lean](../QED/Frozen/WickModel/IsLSZFormFactorPair.lean),
   and `existsUnique_isLSZFormFactorPair` in
   [LszFormFactorExistsUnique.lean](../QED/Frozen/WickModel/LszFormFactorExistsUnique.lean).

7. **(63.1)–(63.3) and (64.2): charge condition.** The charge condition is
   imposed at $p'=p$ on shell, which is what $q^2=0$ forces for positive-energy
   momenta (p. 379), for every $\mu$ and every pair of Dirac solutions. For
   $e\ne0$ exactly one $Z_1$ satisfies it, and the counterterm changes only the
   first form factor. The statement of (64.2) that $F_1(0)=1$ exactly is proved
   as a limit $q^2\to0^+$ at fixed regulators $m_\gamma,\Lambda\gt0$. A joint
   limit with $m_\gamma\to0^+$ would be false, because the slope of $F_1$ at
   $q^2=0$ grows like $\ln(m/m_\gamma)$. See `IsChargeNormalized` in
   [IsChargeNormalized.lean](../QED/Frozen/OneLoop/IsChargeNormalized.lean),
   `existsUnique_isChargeNormalized` in
   [ChargeConditionExistsUnique.lean](../QED/Frozen/OneLoop/ChargeConditionExistsUnique.lean),
   `isFormFactorPair_vertexOneLoop_iff_vertexFunction` in
   [CountertermShift.lean](../QED/Frozen/OneLoop/CountertermShift.lean), and
   `isFormFactorPair_vertexFunction_dirac_limit` in
   [ChargeNormalizationLimit.lean](../QED/Frozen/OneLoop/ChargeNormalizationLimit.lean).

8. **pp. 383–384, (64.3)–(64.7): the magnetic moment.** The source asserts
   that (64.1) "follows from a quantum action of the form" (64.3). It defines
   the interaction Hamiltonian $H_1$ (64.6) from that action, with the values
   $F_1(0)=1$ and $F_2(0)=\alpha/2\pi$ inserted, and evaluates
   $\mu B\equiv-\langle e|H_1|e\rangle$ (64.7). The library does not use the
   quantum action. It formalizes two definitions of $\mu$, both computed from
   the vertex function, and proves that they agree.
   - **Response definition.** In the field $A=(0,Bx,0)$ of p. 383, for
     on-shell Breit-frame momenta $p=(E,-q/2,0,0)$, $p'=(E,q/2,0,0)$ and
     spin-up spinors, $\bar u_+(p')V^2(p',p)u_+(p)=2im\mu q+o(q)$ as
     $q\to0^+$. For every value of the counterterm exactly one $\mu$ has this
     property.
   - **Source definition.** (64.4)–(64.7) with
     $H_1=-\int d^3x\ \mathbf J\cdot\mathbf A=-B\int d^3x\ x^1J^2(x)$, so that
     $\mu=\int d^3x\ x^1\langle e|J^2(x)|e\rangle/\langle e|e\rangle$. The
     one-electron matrix elements of the current come from the vertex
     function or, in the restated definitions, from the LSZ amplitude
     (Deviation 10), and no form-factor values are inserted.

   For every admissible packet profile the source definition tends to the
   response definition as the packet narrows. With the charge-normalized
   counterterm, both give a Landé factor $g=4m\mu/e$ within any $\eta\gt0$ of
   $2(1+e^2/8\pi^2)=2(1+\alpha/2\pi)$ near the regulator limit. See
   `IsResponseMagneticMoment` in
   [IsResponseMagneticMoment.lean](../QED/Frozen/OneLoop/IsResponseMagneticMoment.lean),
   `existsUnique_isResponseMagneticMoment` in
   [ResponseMagneticMomentExistsUnique.lean](../QED/Frozen/OneLoop/ResponseMagneticMomentExistsUnique.lean),
   `landeFactor_isResponseMagneticMoment_limit` in
   [LandeFactorLimit.lean](../QED/Frozen/OneLoop/LandeFactorLimit.lean),
   `sourceMagneticMoment` in
   [SourceMagneticMoment.lean](../QED/Frozen/OneLoop/SourceMagneticMoment.lean),
   `integrable_and_tendsto_sourceMagneticMoment` in
   [SourceMagneticMomentLimit.lean](../QED/Frozen/OneLoop/SourceMagneticMomentLimit.lean),
   and `landeFactor_sourceMagneticMoment_limit` in
   [SourceLandeFactorLimit.lean](../QED/Frozen/OneLoop/SourceLandeFactorLimit.lean).

9. **(64.4)–(64.10): packets and limits in the source definition.** The source
   uses the Gaussian packet (64.5), normalized so that $\langle e|e\rangle=1$,
   and expands to linear order "since the wave packet is sharply peaked". The
   library uses real, rotationally invariant packets
   $f(\mathbf k)=\varphi(|\mathbf k|^2/\lambda^2)$, with $\varphi$ smooth,
   compactly supported and not identically zero on $[0,\infty)$; the Gaussian
   is not of this form. It divides by $\langle e|e\rangle$ instead of
   normalizing $f$. "Sharply peaked" is the limit $\lambda\to0^+$, the
   corrected regime of Erratum 5. The position integral defining $\mu$ is the
   undamped integral produced by the non-decaying potential $A=(0,Bx,0)$.
   Where the source integrates by parts and states that "the wave packets kill
   any surface terms" (after (64.9)), the library proves that the integral
   converges absolutely for every $\lambda\gt0$. The current density is taken
   at time $0$. The packet limit comes first, at fixed regulators and
   counterterm, and the regulator limits afterwards. See `packetCurrentDensity`
   in [PacketCurrentDensity.lean](../QED/Frozen/OneLoop/PacketCurrentDensity.lean),
   `packetNormSq` in [PacketNormSq.lean](../QED/Frozen/OneLoop/PacketNormSq.lean),
   and `integrable_and_tendsto_sourceMagneticMoment`.

10. **Fig. 63.1 and (64.8): current matrix elements.** In the source the
    external electron lines carry "the unit residue of the pole" (caption of
    Fig. 63.1), which the on-shell conditions $\Sigma(-m)=\Sigma'(-m)=0$
    ((62.27), (62.36)–(62.38)) secure, and (64.8) evaluates the one-electron
    matrix element of the current with free spinors. Both magnetic-moment
    definitions of Deviation 8 take this matrix element to be
    $\bar u_+(k')V^\mu(k',k)u_+(k)$: the vertex function between on-shell
    spinors, with unit electron residues and no photon-leg factor. This
    identification remains part of those definitions, and the charge
    condition of Deviation 7 is stated, as in (63.1), for the vertex function.

    The library also derives the current matrix element from the Wick
    expansion. It defines the LSZ amplitude $M^\mu_{s's}(p',p)$ of the
    connected three-point function of the general model (Deviations 4 and
    15). It proves that the electron on-shell conditions fix $\delta_2$ and
    $\delta_m$ uniquely, and that with them the corrections on the electron
    legs vanish at the mass shell. So the residues are one, and $M$ is
    $\bar u_{s'}(p')V^\mu(p',p)u_s(p)$, with $Z_1=1+\delta_1$, plus the
    photon-leg term of Deviation 14. The charge condition and both
    magnetic-moment definitions are then restated with $M$ in place of the
    vertex sandwich, and each restatement is proved equivalent to the
    original. The restated charge condition holds exactly when
    $Z_1=1+\delta_1$ satisfies the original one. A real $\mu$ is a response
    magnetic moment for $M$ exactly when it is one for the vertex function at
    $Z_1=1+\delta_1$. The restated source definition converges absolutely for
    every packet width and tends to the restated response definition as the
    packet narrows. The photon-leg term contributes to none of them
    (Deviation 14). See `electronCounterterms_existsUnique` in
    [ElectronCountertermsExistsUnique.lean](../QED/Frozen/WickModel/ElectronCountertermsExistsUnique.lean),
    `lszAmplitude_eq` in
    [LszAmplitudeEq.lean](../QED/Frozen/WickModel/LszAmplitudeEq.lean),
    `IsLSZChargeNormalized` in
    [IsLSZChargeNormalized.lean](../QED/Frozen/WickModel/IsLSZChargeNormalized.lean),
    `isLSZChargeNormalized_iff_isChargeNormalized` in
    [IsLSZChargeNormalizedIff.lean](../QED/Frozen/WickModel/IsLSZChargeNormalizedIff.lean),
    `IsLSZResponseMagneticMoment` in
    [IsLSZResponseMagneticMoment.lean](../QED/Frozen/WickModel/IsLSZResponseMagneticMoment.lean),
    `isLSZResponseMagneticMoment_iff_isResponseMagneticMoment` in
    [IsLSZResponseMagneticMomentIff.lean](../QED/Frozen/WickModel/IsLSZResponseMagneticMomentIff.lean),
    `lszSourceMagneticMoment` in
    [LszSourceMagneticMoment.lean](../QED/Frozen/WickModel/LszSourceMagneticMoment.lean),
    and `integrable_and_tendsto_lszSourceMagneticMoment` in
    [LszSourceMagneticMomentLimit.lean](../QED/Frozen/WickModel/LszSourceMagneticMomentLimit.lean).

11. **(38.12), (63.1) and (63.18): spinors and spin labels.** The library's
    spinor is the closed form $u_s(p)=(m-\not p)\ u_s(0)/\sqrt{2m(m+p^0)}$, and
    it proves that this equals the boosted rest spinor
    $\exp(i\eta\ \hat{\mathbf p}\cdot\mathbf K)\ u_s(0)$ of (38.12) for
    $\mathbf p\ne0$. The charge condition and the form-factor decomposition are
    stated for all solutions $u$ of $(\not p+m)u=0$ and $\bar u'$ of
    $\bar u'(\not p'+m)=0$ instead of for spin labels $s,s'$. On shell these
    solution spaces are spanned by the $u_s(p)$ and the $\bar u_{s'}(p')$, so
    the conditions are the printed ones for all spins. The LSZ forms of the
    charge condition and of the form-factor decomposition,
    `IsLSZChargeNormalized` and `IsLSZFormFactorPair`, are stated for spin
    labels, as printed. Their agreement with the forms for all solutions is
    proved: for the charge condition by
    `isLSZChargeNormalized_iff_isChargeNormalized`, and for the decomposition
    through the completeness relation (38.23) (see the proof-route section).
    See `spinor` in
    [Spinor.lean](../QED/Frozen/Algebra/Spinor.lean) and `spinor_eq_exp_boost`
    in [SpinorBoost.lean](../QED/Algebra/SpinorBoost.lean).

12. **Throughout: Lean conventions.** The source's conventions are used
    unchanged: the metric $\mathrm{diag}(-1,1,1,1)$, Weyl-representation gamma
    matrices with $\lbrace\gamma^\mu,\gamma^\nu\rbrace=-2g^{\mu\nu}$, $\bar uu=2m$ and the
    vertex $ie\gamma^\mu$. The theorems hold for every real $e\ne0$; the
    physical electron charge $e\lt0$ is a special case. Lean definitions are
    total functions, so they also return values outside the source's domain
    (for example $\epsilon\le0$, off-shell momenta or non-positive masses).
    Those values have no meaning. The source-facing definitions either take
    the domain conditions (positive masses, mass shell, positive energy) as
    arguments or are used only in statements that assume them. The Lean
    integral returns $0$ for a non-integrable integrand; the integrability of
    the one-loop integrand at every $\epsilon\gt0$ is part of
    `vertexLimit_existsUnique`, so the energy-first integrals in the statements
    are genuine integrals on the source's domain. Likewise, the integrability
    at every $\epsilon\gt0$ of each one-loop contraction that enters the
    self-energy, the vacuum polarization and the connected three-point
    function is part of `selfEnergy_existsUnique`,
    `vacuumPolarization_existsUnique` and `lszAmplitude_existsUnique`. The
    coefficient is written $e^2/8\pi^2=\alpha/2\pi$; no expansion parameter is
    introduced.

13. **(62.12)–(62.25), pp. 371–372: the closed fermion loop.** The source
    computes the vacuum polarization (62.12)–(62.23) in $d=4-\varepsilon$
    dimensions, and the condition $\Pi(0)=0$ (62.11) then fixes $Z_3$ (62.24).
    The Pauli–Villars photon of Deviation 1 does not regulate this loop, which
    has no internal photon. The library adds two Pauli–Villars regulator
    fermions, of masses $M_1,M_2\gt m$, as fields of the model. Each couples
    to the photon with the same charge as the electron, through a gauge
    vertex $e\bar\Psi_f\not A\Psi_f$, and a closed loop of flavor $f$ carries
    a coefficient $c_f$, with $c_0=1$ and $M_0=m$ for the electron and
    $$1+c_1+c_2=0,\qquad m^2+c_1M_1^2+c_2M_2^2=0.$$
    The counterterms act on the electron alone. In each contraction the
    flavors of a closed loop are summed inside one loop integrand, before the
    loop integral is taken. This is the same Wick sum, regrouped, and the
    regrouping is needed: a single flavor's vacuum-polarization loop is not
    integrable under the energy-first prescription of Deviation 3, so
    integrating flavor by flavor would give the value $0$ that the Lean
    integral assigns to a non-integrable integrand (Deviation 12). With both
    conditions the regulated loop is integrable at every $\epsilon\gt0$, and as
    $\epsilon\to0^+$ it tends to the transverse form (62.7),
    $\Pi^{\mu\nu}(k)=\Pi(k^2)(k^2g^{\mu\nu}-k^\mu k^\nu)$, for a unique function
    $\Pi$ on $k^2\gt-4m^2$, below the pair threshold. The transversality
    (62.6), which the source takes as given and recovers at one loop in
    (62.21), is part of this theorem. The function $\Pi$ includes the
    counterterm $-\delta_3$, and $\Pi(0)=0$ holds for exactly one $\delta_3$.
    The library shows that this value is $\Pi_{\mathrm{loop}}(0)$, where
    $$\Pi_{\mathrm{loop}}(s)=\frac{e^2}{2\pi^2}\int_0^1dx\ x(1-x)\sum_fc_f\log\bigl(M_f^2+x(1-x)s\bigr).$$
    Since $\int_0^1x(1-x)\,dx=1/6$, this gives
    $$\delta_3=\frac{e^2}{12\pi^2}\sum_fc_f\log M_f^2,$$
    the regulated analogue of (62.24). This last evaluation is not a Lean
    theorem. The regulator fermions do not enter the vertex function at this
    order, since a one-particle-irreducible contraction of the vertex has no
    closed fermion loop, and they do not enter the one-loop self-energy. In
    the LSZ amplitude they enter only through $\Pi$ on the photon leg, which
    changes neither $F_2$ nor $g$ (Deviation 14). Their masses stay fixed; the
    limit $M_f\to\infty$ is not taken. See `Params` in
    [Params.lean](../QED/Frozen/WickModel/Params.lean), `regulatedAmplitude` in
    [RegulatedAmplitude.lean](../QED/Frozen/WickModel/RegulatedAmplitude.lean),
    `vacuumPolarization_existsUnique` in
    [VacuumPolarizationExistsUnique.lean](../QED/Frozen/WickModel/VacuumPolarizationExistsUnique.lean),
    `vacuumPolarization` in
    [VacuumPolarization.lean](../QED/Frozen/WickModel/VacuumPolarization.lean),
    `IsPhotonOnShell` in
    [IsPhotonOnShell.lean](../QED/Frozen/WickModel/IsPhotonOnShell.lean), and
    `photonCounterterm_existsUnique` in
    [PhotonCountertermExistsUnique.lean](../QED/Frozen/WickModel/PhotonCountertermExistsUnique.lean).

14. **(64.3)–(64.7), pp. 383–384, and (62.10)–(62.11): the external photon.**
    In section 64 the photon is "a classical field", $A=(0,Bx,0)$ (p. 383),
    not an asymptotic particle, and its coupling to the electron is read off
    the vertex function, (64.1)–(64.3). The library treats the photon of the
    three-point function as such a background field. Its leg is amputated by
    the free photon propagator and keeps the one-loop vacuum-polarization
    insertion, counterterm included; the LSZ formulas for photons
    (56.1)–(56.8) are not used. Between on-shell spinors the term
    $q^\rho q^\mu$ of $\Pi^{\rho\mu}(q)$ drops out, since
    $\bar u(p')\not q\,u(p)=0$, and the LSZ amplitude is
    $$M^\mu_{s's}(p',p)=\bar u_{s'}(p')V^\mu(p',p)u_s(p)+e\,q^2D(q^2)\,\Pi(q^2)\ \bar u_{s'}(p')\gamma^\mu u_s(p),\qquad D(q^2)=\frac{1}{q^2+m_\gamma^2}-\frac{1}{q^2+\Lambda^2},$$
    with $q=p'-p$, $V^\mu$ the vertex function at $Z_1=1+\delta_1$, $D$ the
    scalar part of the photon propagator of Deviation 1 at $\epsilon=0$, and
    $\Pi$ the vacuum polarization of Deviation 13. The formula holds for every
    value of $\delta_3$. It differs from the form
    $e\Pi(q^2)\bar u'\gamma^\mu u$ that the source's massless, unregulated
    photon would give, with $D(q^2)=1/q^2$, and that vanishes at $q^2=0$
    because of $\Pi(0)=0$: here the factor $q^2D(q^2)$ tends to $1$ only in
    the regulator limit at fixed $q^2\gt0$. The second term is a multiple of
    $\bar u'\gamma^\mu u$, so it changes only the first form factor. In the
    order of limits used here, $q\to0$ at fixed $m_\gamma\gt0$ (Deviation 2),
    it drops out for every $\delta_3$. Like $q^2$, it vanishes to second order
    in $p'-p$ at $p'=p$, so it contributes neither to the charge condition nor
    to the source definition of the magnetic moment; in the Breit frame of
    the response definition it is $ieq^3D(q^2)\Pi(q^2)=O(q^3)$. The photon
    on-shell condition $\Pi(0)=0$ (62.11), although it is proved to fix
    $\delta_3$ uniquely (Deviation 13), is therefore not used for $g$, and the
    headline theorem holds for every $\delta_3$. The condition would matter if
    $m_\gamma\to0$ were taken before $q\to0$, since $q^2D(q^2)$ then tends to
    $1$. See
    `lszAmplitude_existsUnique` in
    [LszAmplitudeExistsUnique.lean](../QED/Frozen/WickModel/LszAmplitudeExistsUnique.lean),
    `lszAmplitude_eq` in
    [LszAmplitudeEq.lean](../QED/Frozen/WickModel/LszAmplitudeEq.lean), and
    `isLSZResponseMagneticMoment_iff_isResponseMagneticMoment` in
    [IsLSZResponseMagneticMomentIff.lean](../QED/Frozen/WickModel/IsLSZResponseMagneticMomentIff.lean).

15. **(62.27), (62.36)–(62.38), (41.17) and (41.25): on-shell conditions and
    the LSZ limit.** The source states the on-shell conditions
    $\Sigma(-m)=\Sigma'(-m)=0$ for the self-energy as a function of $\not p$
    (62.27), and in differentiating takes $p^2=-\not p^2$ (before (62.38)).
    The library first proves the covariant decomposition of the regulated
    one-loop self-energy (62.28). For $m,m_\gamma,\Lambda\gt0$ its loop
    integrands are integrable at every $\epsilon\gt0$, and as $\epsilon\to0^+$
    it tends to $A(p^2)\not p+B(p^2)m$ for a unique pair of functions on
    $p^2\gt-(m+\min(m_\gamma,\Lambda))^2$, below the thresholds of the electron
    with either photon. The library then defines
    $\Sigma(z)=A(-z^2)z+B(-z^2)m$ for real $z$ with
    $|z|\lt m+\min(m_\gamma,\Lambda)$, the source's $\Sigma(\not p)$ with
    $p^2=-\not p^2$, and states both conditions literally at $z=-m$, the
    eigenvalue of $\not p$ on the electron spinors. The derivative is that of
    $\Sigma$ composed with the clamp of $\mathbb R$ onto
    $[-m-\mu/2,-m+\mu/2]$, $\mu=\min(m_\gamma,\Lambda)$. This interval lies in
    the domain and has $-m$ in its interior, so the clamp does not change the
    derivative at $-m$. For all values of the other parameters exactly one
    pair $(\delta_2,\delta_m)$ satisfies the two conditions, as the source
    says after (62.27).

    The source obtains amplitudes from the position-space LSZ formula
    (41.17), with the field normalization (41.25) that the unit residue
    secures. The library defines the LSZ amplitude of the electron current in
    momentum space, as an iterated limit. Let $G^\mu_\epsilon(r',r)$ be the
    connected three-point function of order $e^3$, amputated by the free
    external propagators, with the corrections on the external legs kept.
    First $\epsilon\to0^+$ in $(1/i)\,\bar u_{s'}(p')G^\mu_\epsilon(r',r)u_s(p)$
    at off-shell momenta $r'$, $r$; then $(r',r)\to(p',p)$ through off-shell
    momenta, along every approach. The spinors stay at the on-shell limit
    momenta $p'$, $p$. For $m,m_\gamma,\Lambda\gt0$, regulator fermions as in
    Deviation 13 and the electron on shell, the library proves that every
    one-loop contraction of this function is integrable at every
    $\epsilon\gt0$ and all momenta, and that the iterated limit exists and is
    unique. In the source the external legs carry exact propagators with unit
    residue; here the leg corrections are kept and proved to vanish at the
    shell (see the proof-route section). See `selfEnergy_existsUnique` in
    [SelfEnergyExistsUnique.lean](../QED/Frozen/WickModel/SelfEnergyExistsUnique.lean),
    `selfEnergyAB` in [SelfEnergyAB.lean](../QED/Frozen/WickModel/SelfEnergyAB.lean),
    `selfEnergySlash` in
    [SelfEnergySlash.lean](../QED/Frozen/WickModel/SelfEnergySlash.lean),
    `IsElectronOnShell` in
    [IsElectronOnShell.lean](../QED/Frozen/WickModel/IsElectronOnShell.lean),
    `electronCounterterms_existsUnique` in
    [ElectronCountertermsExistsUnique.lean](../QED/Frozen/WickModel/ElectronCountertermsExistsUnique.lean),
    `lszAmplitude_existsUnique` in
    [LszAmplitudeExistsUnique.lean](../QED/Frozen/WickModel/LszAmplitudeExistsUnique.lean),
    and `lszAmplitude` in [LszAmplitude.lean](../QED/Frozen/WickModel/LszAmplitude.lean).

## "QED Vertex Correction" notes

The notes use the metric $\mathrm{diag}(1,-1,-1,-1)$ and dimensional
regularization. The library uses them only as a guide to steps that the
primary source leaves out; no formal statement is taken from them.

### Errata

1. **(25), p. 6.** Wrong index (misprint). The Gordon identity is printed
   $(p'+p)^\mu\cong2m\gamma^\mu-i\sigma^{\mu\nu}q_\mu$, in which $\mu$ is both
   free and summed. Read $-i\sigma^{\mu\nu}q_\nu$, as in (22) on the same page.
   No effect on the stated theorems.

2. **p. 8, the sentence before (37).** Wrong value (misprint). The text reads
   "The electric form factor $F_1\equiv F_{el}$ for $q^2=1$ is constrained by
   the Ward identity". Read $q^2=0$: (37) itself takes the limit $q^2\to0$, and
   (36) and (38) are evaluated at $q^2=0$. No effect on the stated theorems.

### Deviations

None.

## How the formal proof route differs from the primary source

- **Feynman parameters.** The formula (14.9)–(14.11), whose proof the source
  leaves to problem 14.1, is proved for any three complex denominators in the
  open lower half-plane. The parameters run over the unit square, with
  $x_1=yx$, $x_2=y(1-x)$, $x_3=1-y$ and weight $2y$
  (`inv_mul_mul_eq_integral_feynmanMeasure` in
  [FeynmanParameter.lean](../QED/Integration/FeynmanParameter.lean)). The shift
  used in the reduction exchanges the roles of the source's $x_1$ and $x_2$ in
  (62.43); only the coefficient of $(p'-p)^\mu$, which integrates to zero,
  changes sign.
- **Energy integrals instead of the Wick rotation.** For $w$ off $[0,\infty)$,
  $\int dt\ (-t^2+w)^{-3}=-\tfrac{3\pi}{8}(-w)^{-5/2}$ and
  $\int dt\ t^2(-t^2+w)^{-3}=-\tfrac{\pi}{8}(-w)^{-3/2}$ are proved by holomorphy
  in $w$ and the identity theorem, starting from real $w\lt0$; no contour is
  deformed (`integral_neg_sq_add_zpow_three` and
  `integral_sq_mul_neg_sq_add_zpow_three` in
  [EnergyIntegral.lean](../QED/Integration/EnergyIntegral.lean)). The
  integrability, the exchange of the energy and Feynman-parameter integrals,
  the energy shift and the limit $\epsilon\to0^+$ are proved in
  [VertexEnergyFirst.lean](../QED/OneLoop/VertexEnergyFirst.lean).
- **Spatial integrals instead of the master integral.** The master integral
  (14.27) is not used. After the energy integral, the integrals over the
  spatial loop momentum are evaluated directly in $\mathbb R^3$, and the
  Pauli–Villars pair gives $2\pi\log(D_2/D_1)$ in place of the pole of (62.49)
  ([SpatialIntegral.lean](../QED/Integration/SpatialIntegral.lean),
  [VertexSpatial.lean](../QED/OneLoop/VertexSpatial.lean)). The symmetric
  integration of (62.18) and (62.47), and the statement on p. 376 that the
  terms linear in the loop momentum integrate to zero, are replaced by the
  vanishing of odd and mixed moments and the isotropy of second moments of
  radial functions on $\mathbb R^3$.
- **Dirac algebra.** The contraction (63.10) (problem 47.2), the on-shell
  reduction (63.13)–(63.14), which the source states without the computation,
  and the Gordon identity (38.18), whose derivation the source sketches in
   (38.19)–(38.20), are proved; see
  `vertexNumeratorMatrix_eq` and `sandwich_vertexNumeratorMatrix_neg_shift` in
  [NumeratorReduction.lean](../QED/OneLoop/NumeratorReduction.lean) and `gordon`
  in [Gordon.lean](../QED/Algebra/Gordon.lean).
- **Form factors.** Existence of the decomposition (63.18) comes from the
  closed form of the vertex; uniqueness comes from the linear independence of
  the two on-shell structures for $q^2\gt0$, proved with traces
  (`eq_zero_of_sandwich_formFactor_eq_zero` in
  [FormFactorIndependence.lean](../QED/Algebra/FormFactorIndependence.lean)).
  The limit of $F_2$ is obtained by dominated convergence on the
  Feynman-parameter integral, not from (63.21)–(63.22)
  ([PauliLimit.lean](../QED/OneLoop/PauliLimit.lean)).
- **Magnetic moment.** For the response definition, the Breit-frame matrix
  element of $J^2$ is $ieq\ (Z_1+A(q^2)+B(q^2))$, where $(A,B)$ is the
  form-factor pair of the one-loop vertex. This gives
  $\mu=e(Z_1+A(0)+B(0))/2m$, and the charge condition gives $Z_1=1-A(0)$
  ([MagneticResponse.lean](../QED/OneLoop/MagneticResponse.lean)). For the
  source definition, the library does not linearize the boost as in
  (64.10)–(64.14). It writes the current density as a Fourier integral of the
  packet amplitude, proves that the first position moment converges absolutely
  and equals a momentum derivative on the diagonal (Fourier inversion at the
  origin), shows that the derivatives of the packet weights cancel there, and
  takes the narrow-packet limit of the resulting weighted average
  ([PacketMomentInversion.lean](../QED/Integration/PacketMomentInversion.lean),
  [PacketLimit.lean](../QED/OneLoop/PacketLimit.lean)).
- **Wick expansion.** The source reads the one-loop diagram off its Feynman
  rules. The library classifies all one-particle-irreducible contractions of
  every vertex sequence of order at most $e^3$. The empty sequence, the single
  two-point counterterms and the two-vertex sequences contribute nothing; the
  single gauge vertex and the single vertex counterterm give the trees
  $i(1+\delta_1)e\gamma^\mu$; for three gauge vertices the irreducible
  contractions are exactly six vertex-correction chains, each with sign $+1$.
  Each chain is then evaluated using the translation invariance of the
  energy-first integral ([Classification.lean](../QED/Wick/Classification.lean),
  [ChainValue.lean](../QED/Wick/ChainValue.lean)).
- **Three-point function.** The library classifies all connected
  contractions of order at most $e^3$ with one external fermion pair and one
  external photon. Besides the one-particle-irreducible part, they are the
  counterterm $-i(\delta_2\not p+\delta_mm)$ and the self-energy loop on
  either electron leg, and the counterterm
  $-i\delta_3(q^2g^{\mu\rho}-q^\mu q^\rho)$ and the vacuum-polarization loop
  on the photon leg; the orderings of the vertices cancel the factor $1/N!$.
  The tadpoles, in which the two fermion fields of one gauge vertex are
  contracted into a closed loop attached to the electron line by a photon of
  zero momentum, vanish exactly at every $\epsilon$. Their loop integrand,
  a trace of $\gamma^\nu$ times one propagator, is odd in the loop momentum,
  and the energy-first integral of an odd function is $0$. The two-point
  functions are classified in the same way and give (62.28) and (62.12)
  (`connectedFunction_threePoint_eq` in
  [ThreePointClassification.lean](../QED/WickModel/ThreePointClassification.lean),
  `contractionValue_eq_zero_of_selfLoop` in
  [ThreePointClassificationTadpole.lean](../QED/WickModel/ThreePointClassificationTadpole.lean),
  [TwoPointClassification.lean](../QED/WickModel/TwoPointClassification.lean)).
- **Electron legs.** The source does not compute the corrections on the
  external electron legs; it relies on the unit residue. After
  $\epsilon\to0^+$ at an off-shell momentum $r$, the self-energy insertion on
  the incoming leg, counterterm included, contributes
  $\tilde S_0(r)\Sigma(r)u(p)$ next to the vertex factor, with
  $\tilde S_0(r)=(m-\not r)/(r^2+m^2)$ and $\Sigma(r)=A(r^2)\not r+B(r^2)m$.
  The identity $(m-\not r)(\not r+m)=r^2+m^2$, which on a solution of
  $(\not p+m)u(p)=0$ reads $(m-\not r)(\not r-\not p)u(p)=(r^2+m^2)u(p)$,
  gives
  $$\tilde S_0(r)\Sigma(r)=A(r^2)+m\,\frac{(B-A)(r^2)}{r^2+m^2}\,(m-\not r).$$
  The condition $\Sigma(-m)=0$ says $(B-A)(-m^2)=0$, so the quotient tends to
  $(B-A)'(-m^2)$, while $(m-\not r)u(p)\to2mu(p)$; the limit is
  $\Sigma'(-m)u(p)=0$. The outgoing leg is the same with the factors in the
  other order. The vertex part is continuous up to the shell, and the photon
  leg tends to the term of Deviation 14 because
  $\bar u(p')(\not p'-\not p)u(p)=0$
  (`electronPropagator_zero_mul_selfEnergyForm` and
  `tendsto_electronLeg_in_spinor_of_isElectronOnShell` in
  [LszLegs.lean](../QED/WickModel/LszLegs.lean), `lszLimit_closedForm` in
  [LszLimit.lean](../QED/WickModel/LszLimit.lean)).
- **Spin sums.** The completeness relation (38.23),
  $\sum_su_s(p)\bar u_s(p)=m-\not p$, is proved for the library's spinors.
  Since $(m-\not p)u=2mu$ for every solution of $(\not p+m)u=0$, and
  $\bar u'(m-\not p')=2m\bar u'$ for every solution of
  $\bar u'(\not p'+m)=0$, the spinors $u_s(p)$ and $\bar u_{s'}(p')$ span the
  solution spaces, and a sandwich that vanishes on them vanishes on all
  solutions. This identifies the form-factor decomposition of the LSZ
  amplitude, stated for spin labels, with that of the vertex function,
  stated for all solutions, up to the shift of the first form factor by the
  photon-leg term (`sum_vecMulVec_spinor` and `sandwich_eq_zero_of_spinor` in
  [HeadlineSpinor.lean](../QED/WickModel/HeadlineSpinor.lean),
  `lszPair_iff_isFormFactorPair_vertexFunction` in
  [HeadlinePair.lean](../QED/WickModel/HeadlinePair.lean)). For the charge
  condition the argument is more direct: at $p'=p$ the photon-leg term
  vanishes, the vertex sandwich is a multiple of $\bar u\gamma^\mu u$, and
  $\bar u_s(p)\gamma^0u_s(p)=2p^0\ne0$
  ([LszCharge.lean](../QED/WickModel/LszCharge.lean)).

## Outside the scope of the formal statements

- The Ward identity $Z_1=Z_2$ (68.13), which is not used, and independence of
  the gauge parameter: Feynman gauge is used throughout, and the parameter
  $\xi$ of (62.5) does not appear.
- The limit of large regulator-fermion masses. $M_1$ and $M_2$ are fixed
  parameters; they do not affect $F_2$ or $g$, and the vacuum polarization is
  not shown to approach the renormalized form (62.25) as they grow.
- The intermediate results of the dimensionally regularized route,
  (62.13)–(62.24), (62.30)–(62.35), (62.47)–(62.50) and (63.12); the explicit
  forms (62.36)–(62.38) of the renormalized self-energy, and (63.19) and
  (63.21) for $q^2\ne0$; and problem 64.1 on orbital angular momentum.
- The path integral (58.17)–(58.21) and the position-space formulas:
  time-ordered products and the LSZ formula (41.17), which the library
  replaces by the momentum-space limit of Deviation 15.
- The LSZ formulas for external photons (56.1)–(56.8); the photon is a
  background field (Deviation 14).
- All contributions beyond order $\alpha$.

## Sources used only as references

- T. Aoyama, M. Hayakawa, T. Kinoshita and M. Nio, *Prog. Theor. Exp. Phys.*
  2012, 01A107 (INSPIRE copy, SHA-256
  `0a2e1df91a8390a25783982dd5435d17804bb7a26609cc044c59d00bff57fa91`). The
  library does not use its magnetic projector. As printed, the projector
  (4.4), p. 12, gives $\mathrm{Tr}(P_\nu\Gamma^\nu)=F_2/m$ and annihilates the
  $F_1$ structure; $P^\nu$ has the dimension of an inverse mass. It therefore
  returns $F_2$, as in (4.2), only in units where the lepton mass is $1$,
  which the paper uses without stating them (for example in (7.2), where
  $V=z_1-G$ is its general $V$ with lepton mass $1$). This is a units
  convention, not counted as an erratum.
- M. Knecht, *Lect. Notes Phys.* 629 (2004) 37–84, arXiv:hep-ph/0307239v1
  (SHA-256 `0b82943d67eb0354267ac5fa5dfa81374a9a702ef648da5edf00a9b4b9d48c56`),
  and H. Liu, MIT OCW 8.324 (Fall 2010), Lecture 15 (SHA-256
  `4bf21df5c5e65c7ff8b1b5e901b1d24d7e154ca505f8fbb79d6053b1df8b045b`):
  background only. No entries.
