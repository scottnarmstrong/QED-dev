# What does it mean to prove a QED calculation?

[Campaign HQ](../README.md) · [Project outline](PROJECT-OUTLINE.md)

**A proved QED calculation establishes that a specified mathematical model,
with specified computational prescriptions and inputs, has a stated result.**
An experimental test then asks whether that result describes what is measured.
These are connected achievements, with different kinds of evidence.

Our purpose is to make the computational part of precision physics checkable:
the interaction determines amplitudes, the amplitudes determine coefficients,
and the coefficients and physical inputs determine a prediction. A proof should
follow that chain far enough to support the claim attached to it.

This document explains the campaign's intended meaning of proof. The exact
regulator, renormalization route, and source-facing Lean declarations still
need to be selected and reviewed. The formulas below explain the mathematics;
they are not approved or frozen Lean declarations.

## 1. The claim has a model, an order, and a scope

Consider the electron anomaly, $a_e=(g_e-2)/2$. Write $r=\alpha/\pi$. A first
target is:

> In the specified formulation of renormalized perturbative QED, the coefficient
> of $r$ in the magnetic anomaly is $1/2$.

This gives the one-loop contribution $\alpha/(2\pi)$. Proving it requires the
definition of the coefficient, the derivation of its amplitude, its evaluation,
and its connection to the magnetic observable. The result is exact at the
specified perturbative order. The measured anomaly also contains higher-order
contributions.

A numerical result can instead state that a specified higher-order coefficient
lies between two rational numbers. That is also an exact mathematical theorem,
even when its interval has nonzero width. Precision physics needs both kinds of
result: symbolic identities and rigorously controlled numerical evaluations.

## 2. What must be specified about the model?

The model starts with the physical degrees of freedom and their interaction.
For orientation, a common gauge-fixed QED Lagrangian density has the form

$$
\mathcal L_\xi=
-\frac14 F_{\mu\nu}F^{\mu\nu}
+\bar\psi(i\gamma^\mu\partial_\mu-m)\psi
-e\bar\psi\gamma^\mu\psi A_\mu
-\frac{1}{2\xi}(\partial_\mu A^\mu)^2
+\mathcal L_{\mathrm{ct}},
$$

where $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$, $\xi\ne0$ is a gauge
parameter, and $\mathcal L_{\mathrm{ct}}$ contains counterterms. Here we use
natural units, $\hbar=c=1$; the sign convention for the coupling must be recorded
when this schematic expression becomes an actual specification.

This expression identifies the theory's ingredients. A computation additionally
needs the following data and constructions:

| Ingredient | What the specification must determine |
| --- | --- |
| Fields and conventions | Spacetime, metric, spinor algebra, statistics, units, and normalization |
| Free theory | Propagators, boundary prescriptions, and the free expectation or contraction operation |
| Interaction | Allowed vertices, coupling normalization, and the formal interaction expansion |
| Singular expressions | Mathematical carriers for propagators and amplitudes, and the operations defined on them |
| Regularization | Treatment of ultraviolet and infrared singularities, parameter domains, and order of limits |
| Renormalization | Counterterm construction, finite normalization conditions, and relation to physical charge and mass |
| Observable | The amplitude or response that represents the measured quantity, and the proof of that interpretation |
| Inputs | Which parameters are supplied by measurement and how their uncertainty is represented |

We use the term **perturbative model** for this precise construction of
coefficients and observables. It need not start from an already constructed
nonperturbative interacting Hilbert-space theory. In particular, the formal
interaction expansion can be defined through free-field contractions without
assuming that an oscillatory infinite-dimensional path integral is an ordinary
measure integral.

Rigorous perturbative frameworks already give mathematical meanings to such
constructions. Perturbative algebraic QFT, for example, uses formal series and
defines renormalization through extensions of time-ordered products. It is a
useful reference for the distinction between perturbative construction and a
nonperturbative theory; choosing our precise computational route remains a
project decision. [Brunetti, Fredenhagen, and Rejzner](https://arxiv.org/html/2512.14227v1)

## 3. Where do the computational rules come from?

There are three different roles for rules.

**Logical rules** are Lean's ordinary rules for mathematical deduction. Physics
does not require changing them.

**Model definitions** specify the objects being studied: the free covariance,
the interaction, formal expansion, and renormalization prescription. Selecting
these objects expresses the physical theory we intend to test.

**Computational rules** are mathematical results about those objects. A Wick
expansion, a gamma-matrix reduction, or an integral substitution becomes a
reusable theorem. A tactic can apply that theorem and discharge its conditions.
The resulting proof is checked in the same way as other Lean mathematics.

We can also represent the calculational language explicitly. Let $E$ be an
expression and $\llbracket E\rrbracket_M$ its mathematical interpretation in
model $M$. A sound rewrite system establishes a statement of the form

$$
\operatorname{Derivable}_M(E,E')
\quad\Longrightarrow\quad
\llbracket E\rrbracket_M=\llbracket E'\rrbracket_M,
$$

with the necessary domain conditions included. For truncations or enclosures,
the corresponding conclusion uses the appropriate congruence or inequality.
This is what makes an automated calculation a mathematical derivation.

A relation on symbolic expressions can be studied before such an interpretation
is available. A proof then certifies derivability in that symbolic system. The
stronger claim about QED coefficients additionally needs the interpretation and
its soundness theorem.

An abstract model described by properties also needs care: we must construct
the intended objects and establish those properties. A theorem about every
model with contradictory requirements has no physical application. Likewise,
an algebra defined by generators and relations needs the relevant realization
or nontriviality results when its interpretation depends on them.

## 4. Perturbation theory can be exact mathematics

A formal series

$$A(r)=\sum_{n\ge0}a_nr^n$$

is a sequence of coefficients with defined algebraic operations. Its existence
does not assert convergence for any nonzero real $r$. After renormalization, a
scalar observable can have ordinary numerical coefficients; earlier stages may
instead involve operator expressions, distributions, or regulated integrals.
Their permitted products must be specified separately.

Equality through order $N$ means

$$A\equiv B\pmod{r^{N+1}},$$

or equivalently that the coefficients of degrees $0,\ldots,N$ agree. For scalar
series this can be implemented through a quotient by $r^{N+1}$. The statement
is exact, including when the full series diverges.

Operations must track the order they preserve. Differentiating an agreement
through degree $N$ generally leaves agreement only through degree $N-1$.
Division by a series requires an invertible constant term; division by $r$
needs a different statement and loses an order. These conditions belong in the
rules of a reliable perturbative calculator.

An analytic remainder bound is an additional result, such as

$$
|A_{\mathrm{analytic}}(r)-\sum_{n=0}^{N}a_nr^n|
\le K_N r^{N+1},\qquad 0<r<\delta_N,
$$

for an independently defined analytic quantity. Formal coefficients alone do
not imply this bound. Even asymptotic coefficients need not determine a
function uniquely: on $r>0$, adding $e^{-1/r}$ leaves every power-series
asymptotic coefficient unchanged as $r\downarrow0$.

## 5. What does it mean to allow a textbook manipulation?

It means proving the manipulation in its stated setting. Typical obligations
include:

| Manipulation | Required meaning or justification |
| --- | --- |
| Expand the interaction | A defined formal expansion with correct orders and combinatorial factors |
| Apply Wick's theorem | The specified free Gaussian or quasifree contractions, with fermionic signs where required |
| Enumerate diagrams | Coverage of the independently defined contributions, with justified multiplicities |
| Reduce Dirac algebra | Identities in the chosen Clifford algebra and conventions |
| Multiply fields | A defined product on the stated carrier; distributional products require their own justification |
| Shift loop momentum | Translation invariance in a valid regulated integral or a proved identity in the selected prescription |
| Integrate by parts | The required regularity, integrability, and boundary behavior, or an established continuation argument |
| Introduce Feynman parameters | A parameter identity with the appropriate denominator and branch conditions |
| Wick rotate | A justified contour deformation and treatment of poles and limiting prescriptions |
| Remove a regulator | A stated convergence or continuation result with the order of operations controlled |

For a simple example, positive real $A,B$ satisfy

$$
\frac1{AB}=\int_0^1\frac{dx}{[xA+(1-x)B]^2}.
$$

The conditions make the denominator nonzero and the integral well defined.
Using a related identity with complex propagator denominators requires the
corresponding domain and boundary prescription. The real identity alone does
not discharge that obligation.

Dimensional regularization similarly needs a mathematical interpretation in
terms of analytic continuation and dimension-dependent algebra. Writing
$d=4-\varepsilon$ does not define an ordinary space $\mathbb R^d$ of noninteger
dimension. The selected prescription must justify its integration and algebraic
rules together.

The goal is to prove such results once and make ordinary computations use them
automatically. Their conditions become part of the calculator's operation.

## 6. What is being proved about renormalization?

Regularization gives a precise treatment of singular expressions. Renormalization
specifies subtractions and normalization conditions that define the coefficients
of the chosen physical model. A successful result establishes that this
construction produces the stated finite amplitude or coefficient.

The prescription must define a well-defined operation. If it specifies an
object by conditions, the required existence and uniqueness results must be
established. An instruction to choose counterterms so that the desired
properties hold leaves those results as proof obligations.

Depending on the route, the proof may show convergence after counterterm
subtraction, cancellation of poles in a meromorphic regulator, or existence of
an extension of distributions. Each route has its own mathematical objects.
Algebraic cancellation of regulator poles and existence of a numerical integral
are separate claims unless a theorem connects them.

The finite parts matter. The normalization conditions must identify the charge,
mass, and observable used in the prediction. Relations between schemes require
the corresponding parameter conversion and re-expansion at the stated order;
raw intermediate coefficients need not coincide. Symmetry identities, including
the Ward-Takahashi identities where used, are properties to establish at the
appropriate stage of the construction.

We must also specify the allowed interaction terms. Adding an independent Pauli
coupling $\bar\psi\sigma^{\mu\nu}\psi F_{\mu\nu}$ with a freely adjustable
coefficient changes the model and its magnetic-moment prediction. That choice
cannot be concealed inside a prescription whose stated purpose is to predict
the anomaly from QED's charge and masses.

## 7. Why does the vertex calculation measure a magnetic moment?

In parity-preserving QED, the on-shell electromagnetic matrix element between
equal-mass electron spinors can be parameterized, after stripping the overall
charge and using the required normalization, by

$$
\bar u(p')\left[
\gamma^\mu F_1(q^2)
+\frac{i\sigma^{\mu\nu}q_\nu}{2m}F_2(q^2)
\right]u(p),
\qquad q=p'-p,
$$

where $\sigma^{\mu\nu}=\frac{i}{2}[\gamma^\mu,\gamma^\nu]$ in this convention.
The normalization includes the external-leg factors required by the chosen
prescription. A proper vertex without those factors is a different intermediate
object.

With charge normalization $F_1(0)=1$, matching the low-momentum response to the
spin coupling in an external magnetic field gives

$$g_e=2[F_1(0)+F_2(0)],\qquad a_e=F_2(0).$$

These statements initially concern the regulated perturbative amplitudes and
their specified limits. The matching is a mathematical part of the calculation,
which the campaign must prove. The standard computational treatment of the
form factors and magnetic projection is described in
[Aoyama et al., section 4](https://doi.org/10.1093/ptep/pts030).

Our first complete result should derive the formal coefficient

$$[r]F_2(0;r)=\frac12,$$

where $[r]$ means coefficient extraction. This proves the one-loop contribution
$a_e^{(1)}=\alpha/(2\pi)$ through the chain of independently defined objects.
The known answer is the conclusion to prove, not the definition of $F_2$.

## 8. What would a certified numerical computation prove?

Suppose the defined coefficient is a finite sum of renormalized integrals. An
external program can search for useful transformations and generate numerical
certificates. A Lean checker would establish a theorem of the form

$$
\operatorname{check}(M,n,c,L,U)=\mathrm{true}
\quad\Longrightarrow\quad L\le C_n^M\le U.
$$

Here $c$ is the certificate, $M$ fixes the model, coefficient definition, and
parameters such as mass ratios, and $L,U$ can be exact rational bounds.
Acceptance must itself be proved for the concrete certificate under the
project's proof-checking policy. The soundness theorem is conditional until
that check has been established.

Such a certificate may contain interval bounds, subdivisions, polynomial
approximations, and estimates near singular boundaries. The proof must account
for rounding and integration error and connect the checked integrand to the
intended coefficient. Diagram completeness remains a separate obligation:
precisely integrating an incomplete list gives a precise partial contribution.

This distinction matters in existing computations. A 2025 study reported
resolving a discrepancy between five-loop evaluations through increased Monte
Carlo statistics for a subset of integrals. It illustrates why certifying the
symbolic integrand and controlling its numerical evaluation are both useful.
[Aoyama et al.](https://arxiv.org/html/2412.06473v3)

If a randomized method is used, its theorem may instead have the form
$\Pr(|\widehat I-I|\le\epsilon)\ge1-\delta$, under explicit sampling and
integrand assumptions. This describes the algorithm's probability of success.
It does not make every realized estimate a deterministic enclosure.

## 9. How does a finite-order theorem become a prediction?

For independently defined coefficients, the finite-order expression is

$$P_N(\alpha,\rho)=\sum_{n=1}^{N}C_n(\rho)(\alpha/\pi)^n,$$

where $\rho$ contains the relevant mass ratios. Given a joint input region $D$
and certified coefficient information, a theorem can bound $P_N$ uniformly over
all inputs in $D$. For example, writing $\theta=(\alpha,\rho)$ and letting $J$
enclose specified additional contributions, a result can state

$$
\forall\theta\in D,\ \forall b\in J,\qquad
L\le P_N(\theta)+b\le U.
$$

This is a theorem about the finite-order expression and the stated input
regions. If a separate remainder bound $|R|\le\epsilon$ is supplied, then
$P_N(\theta)+b+R$ lies in $[L-\epsilon,U+\epsilon]$. The algebraic implication
does not itself prove that the physical corrections satisfy the premises.

To bound a separately defined fuller model quantity $A$, we additionally need
control of $A-P_N$, together with any additional sectors included in the
comparison. We cannot infer this control just because the last computed term
is small. If it remains an external theory estimate, the final claim must retain
that estimate explicitly and state that its full error guarantee is conditional
on it.

The uncertainty budget therefore records distinct entries: coefficient
evaluation, measured inputs, omitted perturbative orders, and other physical
contributions. A bound for one entry does not discharge the others.

## 10. What does comparison with experiment establish?

Experiments provide observations interpreted through calibration, apparatus
models, and statistical analysis. Lean can verify the mathematics of an adopted
analysis and the propagation of its stated inputs. The provenance of those
inputs and the adequacy of the experimental model remain empirical questions.

A reported value with a standard uncertainty is not automatically a guaranteed
interval containing the true value. If our theorem takes $\alpha\in I$ as an
input hypothesis, its conclusion is conditional on that membership. A
probabilistic interpretation needs the corresponding statistical model and
correlations.

The electron anomaly provides a useful illustration: it can be predicted using
an independently measured $\alpha$, or it can be used with the theory to infer
$\alpha$. The latter inference cannot also serve as an independent test of the
same prediction. The experimental paper explicitly discusses the dependence of
the test on independent measurements of $\alpha$.
[Fan et al.](https://arxiv.org/abs/2209.13084v2)

Thus an eventual comparison states the perturbative order, datasets, external
contributions, uncertainty model, and comparison criterion. A formal proof can
establish that the stated comparison follows from those premises. Agreement
supports the model experimentally; disagreement may expose a computational,
input, experimental, or modeling problem, or motivate a different physical
theory.

## 11. What does Lean check, and what still needs review?

Lean checks the mathematical statement actually encoded, relative to its
definitions and assumptions. Our completed results permit the standard
mathematical axioms `propext`, `Classical.choice`, and `Quot.sound`. They must
not depend on `sorry` or additional physics axioms. Lean's axiom reporting also
tracks extra trust introduced by native computation; a compiled numerical
answer alone does not meet this campaign's proof policy.
[Lean's axiom reference](https://lean-lang.org/doc/reference/latest/Axioms/)

Physical model choices are expressed by mathematical definitions, and any
retained external premises are explicit. We can prove conditional helper
theorems under those premises, but must supply the relevant hypotheses before
claiming a stronger completed result.

An axiom audit alone cannot establish that the theorem says the intended thing.
A theorem may assume its hardest step as a hypothesis, use an unintended
definition, or quantify over an empty class of models while having an ordinary
axiom footprint. Source and statement review must inspect those possibilities,
including assumptions hidden in bundled structures.

A completed project result therefore needs both a checked proof and a reviewed
connection between the formal statement and its stated physical meaning. The
record should identify the model and prescription, perturbative order, exact
Lean export and revision, source correspondence, validation, numerical
precision, and any retained external inputs.

## 12. How to read this campaign's claims

| Claim in HQ | What it should mean |
| --- | --- |
| Symbolic rule proved | The transformation has a checked theorem with explicit semantics and conditions |
| Integral certified | The specified integral has a proved value or enclosure |
| QED coefficient proved | The model-to-amplitude derivation and coefficient evaluation are connected |
| One-loop anomaly proved | The first coefficient and its magnetic-moment interpretation are established |
| Finite-order prediction certified | The stated truncation is bounded for the specified inputs |
| Analytic remainder proved | A separate checked theorem bounds the specified omitted contribution |
| External theory estimate retained | Any error guarantee using that estimate remains conditional on it |
| Experimental comparison verified | The stated comparison follows from its recorded theoretical and experimental premises |

The immediate work is to make the model specification in section 2 concrete
for one full one-loop derivation. The selected prescriptions and exact Lean
definitions will determine the actual proof obligations. The
[project outline](PROJECT-OUTLINE.md#phase-1--fix-the-one-loop-calculation)
sets out that next stage. This explanatory document itself proves no QED
coefficient and does not fix a regulator or freeze a theorem statement.
