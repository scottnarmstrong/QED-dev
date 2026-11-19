# Set (c): deriving the massive-photon kernel inside the campaign (feasibility and plan)

Scratch, untracked. Written 2026-11-19 against `main` at `c216397`. Nothing here is frozen,
approved or staged, and no tracked file was edited. The scripts and their outputs are in this
directory (section 7).

## 0. Summary

**Goal.** Today `QED.Chain.integral_setC_eq_aSetC` proves
`∫₀¹ λ⁽⁴⁾(x) Δα(x) dx = aSetC`, with the Balzani–Laporta–Passera (BLP) kernel
`λ⁽⁴⁾ = κ⁽⁴⁾ − 2(1−x)Δα` as a retained external input. The model link must show that set (c),
as defined by the frozen models, tends to this integral in the D-37 order.

**Route in one paragraph.**
1. Write the renormalized bubble as a superposition of massive photons. This exists in the
   repository, at `ε = 0` and at `ε > 0`.
2. Each spectral component is then a two-loop vertex with one photon of mass² `t`. Sum it over
   the 12 placements (6 non-VP graphs × 2 photon lines) with the matching counterterms:
   - the one-loop massless `δ₁, δ₂, δ_m` (level 0), for placements where the massive photon is
     outside the subdivergent subgraph;
   - the VP share of the order-`e⁴` counterterms (level 1), for placements where it is inside.
3. The key analytic statement is the **Stieltjes identity** (S):

   `A_(c)(t) = ∫₀¹ λ⁽⁴⁾(x) · Q(x)/(Q(x) + t) dx`, with `Q(x) = x²/(1−x)` (`m = 1`),

   where `A_(c)(t)` is that sum, in units of `(α/π)²`. Given (S), the dispersion integral,
   `∫₀¹ ρ(v) A_(c)(4/(1−v²)) dv`, is `∫₀¹ λ⁽⁴⁾ Π̂(Q(x)) dx = aSetC`. This takes only Fubini, the
   proved `QED.Chain.piHat_eq_spectral` and the proved value theorem. (S) is BLP eqs. (18)
   and (20) combined: the dispersion relation of K⁽⁴⁾ with the x ↔ t map
   `t ↔ −t(x) = Q(x)`.
4. Take the remaining limits: the t-integral against the loop limits (`ε`, `q²`, `(m_γ, Λ)`), and
   the decoupling of the bubble's regulator fermions. Once (S) is proved, decoupling follows from
   `|A_(c)(t)| ≤ C(1 + ln t)/t`.

**Numerical status.** Checked numerically, independently of BLP's derivation:
- **The t → 0 end of (S), to 34 digits.** `∫κ⁽⁴⁾ = 2A₁⁽⁴⁾` and `∫λ⁽⁴⁾ = 2(A₁⁽⁴⁾ − A_VP)`.
- **(S) at t = 1 and t = 4.** The left side is built from the repository's own exact parametric
  engine (`scripts/numerics/two_loop_unit_integrals.py`), with separate inner and outer photon
  masses (section 2). It agrees with BLP's kernel to 2.6·10⁻¹³ at t = 1 (level 12) and 2.5·10⁻¹¹ at t = 4
  (level 8). Both are the 3D quadrature floor, which the mirror-pair asymmetry measures.

**Feasibility.** Every ingredient is of a type the repository has already proved once. The new
analytic core is step (iii) of section 1: the fibre reduction proving (S) from the parametric
representation. It is comparable to the Phase 4 exact evaluations of X and C. The model link
(three loops reduced to "two-loop units at a massive photon") is comparable to set (b)'s model
link plus a generalization of the Phase 4 unit links to per-line photon masses.

**Total estimate:** 215–405 Lean files (section 6). Of these, the helper-level kernel derivation
(Stage K) is 60–110 and is independently useful.

**Recommendation.** Do it in two separable stages:
- **Stage K** (helper level, no packet): derive (S) from the parametric two-loop units with
  separate photon masses. This removes the "retained external input" label from κ⁽⁴⁾ as a
  mathematical object.
- **Stage 3c** (packet plus model link). Freeze it only after Stage K's pilot (the L pair)
  closes, and after set (a)'s model link has built the graded-counterterm insertion machinery
  (section 4).

## 1. The mathematical derivation

Notation: `m = 1`; Euclidean `K = −k² ≥ 0`; `F₂(μ) = ∫₀¹ x²(1−x)/(x²+(1−x)μ) dx` is the
one-loop Pauli coefficient at photon mass² `μ` (`QED.TwoLoop.UnitLLink.oneLoopF2`, whose argument
is the mass, not its square). `V_k(μ)` and `V_m(μ)` are the one-loop vertex with a `δ₂` or `δ_m`
insertion on its internal line (`QED.TwoLoop.UnitSCClose.selfVk`, `selfVm`), and
`M_in(μ) = Y² + (1−Y)μ`.

### (i) Bubble → superposition of massive photons: what exists

| Level | Statement | Lean |
| --- | --- | --- |
| `ε = 0`, one flavour | `Π̂(s) = ∫₀¹ ρ(v) s/(s + 4/(1−v²)) dv`, `ρ(v) = v²(1−v²/3)/(1−v²)` | `QED.Chain.piHat_eq_spectral` |
| `ε = 0`, model flavours | `Π_loop(s) − Π_loop(0) = (e²/4π²) Σ_f c_f ∫₀¹ ρ(v) s/(s + 4M_f²/(1−v²)) dv` | `QED.TwoLoop.UnitVPLink.vacuumPolarizationLoop_sub_zero` |
| `ε > 0`, closed form | `Π^{μν}_ε = iΠ̂_ε(k²)(k²g − kk) + ε S_ε g`, `Π̂_ε` with `log(M_f² + x(1−x)s − iε)` | `QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq` (`VPHalfAtInner.lean`) |
| `ε > 0`, spectral | after integration by parts in the bubble parameter `x`, one massive photon-type denominator of mass² `M²/(x(1−x))` and prescription `ε/(x(1−x))` per flavour | `QED.TwoLoop.VPHalfAtGen.specInt*` (`VPHalfAtGenSpec.lean`), `gIntG_eq` (`VPHalfAtGenAssembly.lean`), `gSpec` (`HCBB2Spec.lean`) |
| one-loop outer, `ε → 0` | engine for any list of photon-type denominators with their own prescriptions and any number of spectral insertions, bounds uniform in the spectral parameters | `QED/TwoLoop/VPHalfAtGen*.lean` |
| `q → 0`, spectral component | one-loop vertex with masses `(m_γ, Λ, m_γ, Λ, μ_v)`, `kern5`, continuity in repeated masses | `QED/TwoLoop/VPHalfKernel.lean` |
| `δ₃` | the `δ₃` classes are the constant `Π_loop(0)`; only the subtracted bubble is spectral | `QED.TwoLoop.VPHalf.vpHalf_iff_vpHalfSub` |

**Reusable unchanged:**
- the pointwise-in-`k` identities (closed form, integration by parts, spectral form);
- the `δ₃` bookkeeping;
- the regulator-fermion decoupling pattern (`abs_vpLimSum_sub_le`, `chainLim_sub_bounds`).

**Not reusable as is:**
- everything stated with a one-loop outer integrand: the engine's denominators
  `D_m(p'+k) D_m(p+k)`, and `outerAt`;
- the three-loop Fubini helper `HCNestedFubini`, whose outer factor is one-loop.

**The longitudinal part.** The inserted tensor is `(k²g − kk)Π̂`. Inside a two-loop vertex the
`kk` part does **not** vanish graph by graph, only in the sum over the gauge-invariant set (with
the counterterm graphs and `δ₁ = δ₂`). The massive-photon kernel below uses the Feynman-gauge
massive propagator `g_{μν}/(K + t)`. The numerical check in section 2 confirms that this is the
right object for the set. Its agreement with BLP is evidence that the `kk` parts cancel, but it is
not a proof.

### (ii) The two-loop anomaly with one massive photon

**Graphs and placements.** Of the seven two-loop graphs, L, X, C₊, C₋, S₊, S₋ each have two
photon lines, and the bubble can sit on either: 12 three-loop graphs. On the VP graph's photon
lines it would give the set (b) chain graphs, which `λ⁽⁴⁾` removes. In the hierarchical variables
of `docs/TWO-LOOP-UNITS.md` §2.2, one photon line is **inner** (inside the subdivergent subgraph:
the vertex subgraph of L and C, the self-energy subgraph of S, either line of X) and one is
**outer**. Write `U(μ, ν)` for a unit with inner photon mass² `μ` and outer photon mass² `ν`.
The kernel is

`A_(c)(t) = Σ_{U ∈ {L, X, S, C}} [U(t, 0) + U(0, t)]`, with `S = S₊ + S₋` and `C = C₊ + C₋`
taken as units.

There are 4 × 2 = 8 unit placements; X(t,0) = X(0,t) by the mirror symmetry (checked
numerically to `6·10⁻¹¹`, section 2).

**The splitting identity (2.1) holds verbatim with two masses.** In Feynman gauge the numerator
polynomials `A₂, A₁` of each graph do not depend on the photon masses. The masses enter only the
second Symanzik function. With `w = b(1−x)/x`:

`D = M_in(μ) − ν·e + b·h_ν(x)`, `h_ν(x) = (x² + (1−x)ν)/x`, `e ∈ {0, y₃y₄, z₂z₃}`.

This was verified with the repository's exact engine (`gen.py` reproduces the graphs' `D₀`). The
b-integral over `b ≥ β(x)` is therefore the same combination of the masters `I_{j,n}(β; M, h)`,
at `M = M_in(μ) − νe` and `h = h_ν`. The inner Pauli–Villars subtraction `e₀ = ℓ ln h − c₁/h²`
cancels pointwise against the counterterm's `ln M_Λ`, as before. For the vertex subgraphs
`∫ℓ dx = ½F₂(ν)` holds for every outer mass.

**Unit formulas at `Λ = ∞`.** These are the existing finite-λ formulas (3.4), (5.3), (6.3) of
TWO-LOOP-UNITS, with the inner and outer masses separated; `G_U = E_U − e₀`.
- `L(μ,ν) = ∫dY [∫dx G_L − F₂(ν)(Y(Y²+2Y−2)/(2M_in) − (Y/2) ln M_in)]`;
- `S(μ,ν) = 2∫dY [∫dx G_S + d̄₂(Y;μ) V_k(ν) + d̄_m(Y;μ) V_m(ν)]`;
- `C(μ,ν) = 2∫_{Δ₂} [∫dx G_C − F₂(ν)((Y²+2Y−2)/(2M_in) − ½ ln M_in)]`, with two `x`-branches,
  `β = max(g, ex/(1−x))`;
- `X(μ,ν) = ∫_{Δ₂} ∫dx G_X` (no subtraction: `logc = e₀ = 0` from the engine).

At `μ = ν = 0.01²` these reproduce the documented values: L 0.671406563 (20 digits from this
script), S −4.5793668, and C 3.9267, the documented 3D estimate. X(0,0) reproduces BMR row e) to
1·10⁻⁷ at level 4.

**Counterterms in model terms.**
- *Inner massive* (L(t,0), C(t,0), S(t,0)). The subgraph counterterms are the one-loop on-shell
  constants at photon mass² `t`: `δ₁(t)` for L and C, `δ₂(t)` and `δ_m(t)` for S. In the model
  these are the **VP share** of the level-1 coefficients `d₁ f 1`, `d₂ f 1`, `d_m f 1` of
  `QED.Graded`. By dispersion, `δ^{(4)}_{VP} = ∫ρ δ(t_v) dv`, with the `δ₃` subtraction and the
  photon Pauli–Villars factors. This share is not a model object today; see (G₁₄) in section 3.
- *Outer massive* (L(0,t), C(0,t), S(0,t)). The level-0 constants `δ₁(0)`, `δ₂(0)`, `δ_m(0)`
  multiply the one-loop graphs with the massive photon: `F₂(t)`, `V_k(t)`, `V_m(t)`.
- The `δ₃` partners are absorbed in `Π̂ = Π_loop − Π_loop(0)`.

**The IR structure differs from Phase 4.** Phase 4's IR-finite groupings were L, X and S + C. At
a massive photon the logarithms move between placements:
- L(t,0) ~ `+F₂(t) ln λ`: the outer-soft region, coefficient `∫Yc/M_in = F₂(t)`.
- L(0,t) ~ `−F₂(t) ln λ`: from `δ₁(0)`. So the **L pair** is IR-finite.
- S(0,t) + C(0,t) has `ln λ` coefficient `−2(V_k(t) + V_m(t) + F₂(t))`. This is **zero for
  every photon mass** by the proved `QED.TwoLoop.UnitSCClose.selfVk_add_selfVm_add_oneLoopF2`.
  The same identity drives Phase 4's S + C.
- S(t,0), C(t,0) and X are IR-finite individually.

Numerically, the L pair changes by 9·10⁻¹⁵ between `λ² = 10⁻⁴⁰` and `10⁻⁵⁰`, and S(0,t) +
C(0,t) changes by 7·10⁻¹², the level-8 quadrature floor (section 2).

**What carries over from the A₁⁽⁴⁾ proof.**

| Layer | Phase 4 files | Generalizes to a massive line? |
| --- | --- | --- |
| Wick/class enumeration, routing, `ε → 0` parametric limit | `Enumeration*`, `Routing`, `ClassLimit*`, `TwoLoopParametric*` | the parametric engine is generic in a mass vector; the class data use `pvMasses P` (8 lines, `{m_γ, Λ}` per photon). Extending to `(m_γ, Λ)` on one photon and a signed mass list on the other is mechanical but touches every class file |
| `q → 0` explicit form | `PauliZeroExplicit*` (`openZero c P`) | generic in the masses through `pvMasses`; same extension |
| hierarchical variables, Cheng–Wu, b-masters | `Unit*GraphReduce*`, `Integration/ChengWu*`, `SimplexMerge*` | yes: the polynomial identities do not see the masses; only `D` changes, `M ↦ M_in(μ) − νe`, `h ↦ h_ν`. Note that `M` can be negative for `t > 4` (`M = Y²(1 − t s(1−s))` at `μ = 0`): the masters have removable singularities on that surface, so bounds must use `M + βh > 0`, not `M > 0` |
| counterterm algebra, `δ₁ = δ₂`, `V_k + V_m + F₂ = 0` | `UnitSCCt*`, `UnitSCCloseIR`, `WardIdentity*` | yes; `selfVk_add_selfVm_add_oneLoopF2` is already for every photon mass |
| regulator limits (dominated convergence near corners) | `UnitLLink*`, `UnitXClose*`, `UnitSCLimit*`, `UnitSCCorner*` (~100 files) | must be redone with the extra parameter `t`, uniform in `t` on `[4, ∞)` with an integrable `t`-weight. With one line massive the IR corners are simpler, but uniformity at large `t` is new |
| exact λ = 0 evaluations (x-, ξ-integrations, masters, kernels `K_L, K_S, K_C, K_X`) | `UnitLS`, `UnitC`, `UnitX*`, `UnitXXi*`, `UnitSCCornerX*` | **no**: at `t > 0` new letters (`Q + t`) appear. These are replaced by step (iii) |

### (iii) The closed form: the Stieltjes identity and how to prove it

**Statement (S).** `A_(c)(t) = ∫₀¹ λ⁽⁴⁾(x) Q(x)/(Q(x)+t) dx` for `t > 0`. Equivalently,
`A_(c)(t) = −(1/π)∫₀^∞ dQ Im A_(c)(−Q+i0)/(Q+t)`, with `Im A_(c)(−Q) = −π λ⁽⁴⁾(x_Q)/(dQ/dx)`,
which is BLP (18) and (20) once `λ⁽⁴⁾ = κ⁽⁴⁾ − 2(1−x)Δα` is unwound.

At one loop it is the identity `F₂(t) = ∫(1−x)Q/(Q+t) dx` (`κ⁽²⁾ = 1−x`), i.e. the electron
parameter `x` is BLP's `x`.

**Why it is provable by real analysis.** In each placement the massive mass² enters `D` linearly:
`D = α + βt`, with `β` the massive line's Feynman parameter (`w − e` outer, `1 − Y` inner) and
`α` the massless `V`. So `1/D = β⁻¹/(Q + t)` with `Q = α/β`: every term is a Stieltjes
transform in `t` of the push-forward of the parametric measure under `Q = α/β`. The fibre
`{α/β = Q}` is explicit, and BLP's `x` appears as a range boundary:
- *Outer massive:* `α = M_in + bx`, `β = b(1−x)/x − e`. Solving for `b` gives
  `b = (M_in + Qe)x/(Q(1−x) − x²)`, which requires `x < x_Q`, where `x_Q²/(1−x_Q) = Q`.
- *Inner massive (outer massless):* `α = Y² + bx`, `β = 1−Y`. Then `b = (Q(1−Y) − Y²)/x`, which
  requires `Y < x_Q`.

The proof of (S) is therefore a **fibre integration**: for each unit pair, integrate the
parameters other than `Q` in closed form. The result is a weight-2 function of `x_Q`, and the sum
is `λ⁽⁴⁾(x_Q) dx/dQ`. This is the same kind of work as the Phase 4 `x`-, `b`- and
ξ-integrations:
- rational functions;
- logarithms;
- `Li₂` of rational arguments: `F⁽⁴⁾` has `Li₂(u)`, `Li₂(−u)` and `ln(−u)ln((1−u)²(1+u))`.

Two practical points:
1. *Logs that are not Stieltjes per placement.* The finite parts of `δ(t)` contain
   `ln M_in(t) = ln(1−Y) + ln(Q_Y + t)`, which is not a Stieltjes transform. It cancels inside
   each unit, against the `−ln(M+ch)/h`-type term of the two-loop part, so the fibre densities
   must be taken per unit (graph plus its counterterms), not per graph. The `1/D²` terms give
   `−∂_α`, handled by one integration by parts in `Q` or by working with the b-integrated forms.
2. *Pilot.* The L pair is 2D and has the simplest counterterm. Its fibre density is a 1D
   integral over `Y ∈ (0, x_Q)` (inner) or `x ∈ (0, x_Q)` (outer). It should be done first and
   compared with a numerical split of `λ⁽⁴⁾`: per-unit spacelike densities are not in BLP, so
   they must be computed numerically from section 2's integrands.

**Alternatives considered and rejected.**
- (R2) Analytic continuation in `t` plus the discontinuity, i.e. complex analysis on parametric
  integrals. Mathlib support for this is thin.
- (R3) First the closed form of K⁽⁴⁾(t), BR 1975 eq. (3.21), weight-3 polylogarithms in `t`,
  then (S) as an identity of explicit functions. Harder than the fibre route, and the source
  (Barbieri–Remiddi, Nucl. Phys. B 90 (1975) 233) is not pinned.
- (R4) Evaluating `Σ_P ∫ρ A_P` directly to `aSetC`. This is a new weight-4 reduction that throws
  away the proved one-variable value.

### (iv) Interchanging the t-integral with the loop limits (D-37 order)

1. **ε → 0⁺.** At fixed `ε` the bubble's Feynman parameter `x_b` gives an extra photon-type
   denominator with prescription `ε/(x_b(1−x_b))`. A two-loop outer integrand with **mixed
   prescriptions** is needed. That is a generalization of `ClassLimitParametric` (common `ε`,
   `W = V − iε`) to `W = V − iΣ_i z_i ε_i`. Dominated convergence is unchanged (`|W| ≥ V ≥ c`),
   but the derivation of the parametric form at `ε > 0` (`TwoLoopParametric*`) assumed a common
   `ε` and must be revisited. Bounds must be uniform in `x_b ∈ (0,1)`, as `exists_good_specInt`
   does at one loop: the spectral mass `μ_x² = M²/(x(1−x)) ≥ 4M²` is bounded below.
2. **q² → 0⁺ at fixed regulators.** Per spectral component, through the explicit
   Feynman-parameter form (`openZero` with the extra mass), then Fubini in `x_b`. The pattern is
   `tendsto_outerAt`, with bounds uniform in `μ ≥ 2m`.
3. **(m_γ, Λ) → (0, ∞) jointly, at fixed bubble regulators.** Per spectral parameter `t`, the
   unit limits of (ii) with a third mass. On the bubble line the photon factor is
   `D(K)²K·(K/(t(K+t)))`, which after partial fractions is the five-mass kernel `kern5` with
   masses `(m_γ, Λ, m_γ, Λ, √t)`; repeated masses are handled by continuity. Dominated convergence
   in `t` needs `|A_reg(t; m_γ, Λ)| ≤ C(1 + ln t)/t` for `t ≥ 4`, uniformly in the regulators.
   This is the main new analytic estimate of the model link. The joint `(m_γ, Λ)` uniformity
   issue of Phase 4 (`(m²/Λ²) ln m_γ`, cancelling only in S + C) recurs in S(0,t) + C(0,t). It
   cancels by the same identity, now at the masses `m_γ` and `Λ` of the massless line.
4. **Regulator fermions last.** The flavour-summed spectral weight is `Σ_f c_f ρ(v)` at
   thresholds `4M_f²`. The regulator part is `∫_{t ≥ 4M²} ρ A_(c)` up to `O(M⁻²)`, and it tends
   to 0 because (S) gives `|A_(c)(t)| ≤ ∫|λ⁽⁴⁾| Q/(Q+t) ≤ C(1+ln t)/t`. Here `|λ⁽⁴⁾(x)|` is
   bounded by `C(1 + |ln(1−x)|)`, and `κ⁽⁴⁾(1) = −23/18`. This is the analogue of O3-12, and it
   is cheap once (S) holds. The VP-share counterterms carry the same regulators and decouple
   with them.

**Nested equals joint at three loops (O3-6 analogue).** The inner-first route of
`HCNestedFubini` (`..._innerFirst`) applies with the bubble innermost. It integrates the bubble in
closed form (`VPHalfAtInner`) and leaves a **two-loop** integrand with a logarithmically growing
photon factor. The two-loop Fubini bounds (`TwoLoopRefinedBoundFubini`, `NestedVPFubiniBound*`)
must be re-proved with that factor. Set (b) found the direct route too weak (exponent 17/2
against 13/2) and the inner-first route sufficient. Here the outer factor has one electron loop
more, so the margin must be rechecked by power counting before committing.

**Integrability (the HC₀ analogue).** The 12 three-loop representatives can follow `repBB`: a
common complex rotation (`QED/Integration/ThreeLoopRotation.lean`), elliptic denominators, and
PV-summed bubble decay `ρ⁻⁵`. Numerators reach degree 6. The counterterm representatives are
two-loop and follow `ClassIntegrable*`.

## 2. Numerical checks (mpmath; evidence, not proof)

Scripts in this directory. Every two-loop integrand is generated from the repository's exact
parametric engine (`integrand_parts` and `b_integral` of
`scripts/numerics/two_loop_unit_integrals.py`), with the inner and outer photon masses as separate
symbols.

**Check 0: validation of the two-mass unit formulas at equal masses** (`units2d.py`,
`units3d.py`):

| Unit | this script, `μ = ν = 10⁻⁴` | TWO-LOOP-UNITS |
| --- | --- | --- |
| L | 0.67140656253639147098 | 0.671406563 (§3.3) |
| S | −4.5793668181957424177 | −4.5793668 (§5.3) |
| C | 3.926704 (level 4) | 3.92671 (§6.3, 3D Gauss) |
| X(0,0) | −0.46764534585 (level 4; error 1.0·10⁻⁷, as expected at that level) | −0.467645446093613651 (BMR row e)) |

**Check 1: the t → 0 end of (S)** (`blp.py`, 40 digits). At `t = 0` every placement is the
massless graph, so `A_(c)(0) = 2(A₁⁽⁴⁾ − A_VP)`:

| Quantity | Value | Difference |
| --- | --- | --- |
| `∫₀¹ κ⁽⁴⁾` | −0.65695793115838756916434563392978533 | — |
| `2A₁⁽⁴⁾` | −0.65695793115838756916434563392978478 | 5.5·10⁻³⁴ |
| `∫₀¹ λ⁽⁴⁾` | −0.68833277487659293438579607845679569 | — |
| `2(A₁⁽⁴⁾ − A_VP)` | −0.68833277487659293438579607845679514 | 5.5·10⁻³⁴ |

The common 5.5·10⁻³⁴ is the quadrature floor at 40 digits. This confirms:
- the placement counting (each non-VP graph twice);
- that BLP's `κ⁽⁴⁾` includes the two chain graphs and `λ⁽⁴⁾` removes exactly them;
- the normalization of `A_(c)`.

**Check 2: (S) at finite t** (`run2d.py`, `run3d.sh`; L and S on fixed tanh-sinh rules at
level 8 with geometric breakpoints, 25 digits; C and X on product rules at level 8 / x-level 16,
30 digits; the massless line at `λ² = 10⁻⁴⁰` and `10⁻⁵⁰` in L and S and in the corner
counterterm, exactly 0 in the C and X two-loop parts):

| piece | t = 1 | t = 4 |
| --- | --- | --- |
| L(t,0) + L(0,t) | 0.26258700006241742592 | 0.12930975055018345828 |
| S(t,0) | −0.59998526940548416844 | −0.28672402713348323948 |
| S(0,t) + corner counterterm C_ct(0,t) | −0.50454859727102341676 | −0.26243446414769337995 |
| C(t,0) | 0.27387695525335397267 | 0.098856526607211374534 |
| C(0,t), two-loop part | 0.12735797238608204755 | 0.034621139168420099969 |
| X(t,0) | −0.019753240328477760096 | −0.0059973903920576577365 |
| X(0,t) | −0.019753240271253305679 | −0.0059973903888529924874 |
| **A_(c)(t), sum** | **−0.48021841957438520484** | **−0.29836585573627233688** |
| **∫₀¹ λ⁽⁴⁾ Q/(Q+t) dx (BLP)** | **−0.48021841969015085453** | **−0.29836585576128851898** |
| difference | 1.16·10⁻¹⁰ (2.4·10⁻¹⁰ relative) | 2.5·10⁻¹¹ (8·10⁻¹¹ relative) |
| error indicator: X(t,0) − X(0,t) (equal by mirror symmetry) | −5.7·10⁻¹¹ | −3.2·10⁻¹² |

The differences are at the size of the 3D quadrature error, which the mirror pair X(t,0) and
X(0,t) measures independently. At level 8, (S) holds to 9.6 significant digits at `t = 1` and 10.1 at
`t = 4`. The left side contains no BLP input. The level is too low for 15 digits. The level-8
3D product rule costs 5–8 min per unit on 3 cores (C and X at 30 digits); level 12/24 for `t = 1`
was rerun at level 12/24 (3D) and level 12 (2D) at `t = 1`:

| piece (t = 1, level 12) | value | change from level 8 |
| --- | --- | --- |
| L pair | 0.2625870000624329597 | 1.6·10⁻¹⁴ |
| S(t,0) | −0.5999852694054830181 | 1·10⁻¹⁵ |
| S(0,t) + C_ct (level 12; level 16 differs by 8.7·10⁻¹⁵) | −0.5045485973199926128 | 4.9·10⁻¹¹ |
| C(t,0) | 0.2738769552533539609 | 1.2·10⁻¹⁷ |
| C(0,t), two-loop part | 0.1273579723764830851 | 9.6·10⁻¹² |
| X(t,0) / X(0,t) | −0.0197532403284691952 / −0.0197532403282264214 | 8.6·10⁻¹⁵ / 5.6·10⁻¹¹ |
| **A_(c)(1)** | **−0.4802184196898925472** | |
| **BLP Stieltjes** | **−0.4802184196901508545** | |
| difference | **2.6·10⁻¹³** (12.3 digits) | |

The residual equals the remaining mirror asymmetry X(0,t) − X(t,0) = 2.4·10⁻¹³. With the better
converged X(t,0) used for both mirror placements, the difference is 1.6·10⁻¹⁴ (13.5 digits).
Reaching 15 digits needs level 16/32 for X(0,t) and C(0,t), about 1 h per unit on 3 cores. That is
not run, because the check is already decisive.

**IR stability.** Between `λ² = 10⁻⁴⁰` and `10⁻⁵⁰` at `t = 1`:
- the L pair changes by 9·10⁻¹⁵, although L(t,0) and L(0,t) each move by 1.20, their `F₂(t) ln λ`
  terms;
- S(t,0) changes by 1·10⁻¹⁵;
- S(0,t) + C_ct(0,t) changes by 7·10⁻¹² (each moves by 2.4). This is the level-8 cancellation
  floor; the expected `O(λ ln λ)` residue is < 10⁻¹⁸.

At `λ² = 10⁻²⁰` and `10⁻³⁰` (level 6) the S + C pair moved by 1·10⁻⁸ = `O(λ ln λ)`, as expected.
`V_k(4) + V_m(4) + F₂(4) = 3·10⁻²⁸`: the identity behind the S + C cancellation, at a massive
photon.

**Pitfall recorded.** With breakpoints only at `√λ` and `λ^{1/4}`, the 1/Y-type counterterm
integrands over 20 decades gave errors of 10⁻³ in S(0,t). Geometric breakpoints (factor 100)
fixed this. A Lean proof faces the same issue as a uniformity question, not a numerical one.

## 3. Frozen statements needed (a Stage 3c packet)

The STAGE2-DESIGN deferral D2 already names the slot: "(G₁₄) `ctVPShare`, (G₁₅) `vertexSetC`,
the split theorem — set (c) packet (Stage 3c); (G₆) already accepts grading-reading
selections". D-52.5 requires an L = 3 scope audit and an amendment for any new family. A
candidate packet, in the D-53 pattern:

| Id | Kind | Content |
| --- | --- | --- |
| (Sc₀) | ruling | D-52 amendment: (T₁₀)/(F₇) scope extended to the set (c) contractions at `K = 7` inside the graded selected part (G₆), and to each one individually in (Sc₉). Audit of `IsChord`, `loopCount`, routing and value at L = 3 is already done (D-52); the new content is the graded counterterm vertices at level 1 |
| (Sc₁) | def | `IsSetC`: an explicit witness, as for `IsVPChain`. Open line with the external photon; a two-loop skeleton among {ladder, crossed, corner, side} (not VP), or its one-loop reduction by an order-`e²` counterterm vertex; exactly one VP slot (a two-vertex electron bubble or a `photonCt`) on one photon line. Plus the one-loop vertex with one level-1 counterterm vertex (VP share). Expected ≈ 39 relabelling orbits: 12 bubble, 12 `δ₃`, 5 + 5 one-loop with an `e²` counterterm and bubble or `δ₃`, and 5 with a level-1 share counterterm |
| (G₁₄) | def + goal | `ctVPShare`: the level-1 coefficients `d₁^VP, d₂^VP, d_m^VP` of the electron block, defined by the family-restricted order-`e⁴` on-shell and charge conditions: (G₉) and (G₁₀) with `selfEnergyPart` and `vertexPart` restricted to the "one-loop graph with VP slot" family. Goal: `∃!` (the (G-ex₂) pattern), plus the share Ward identity `d₁^VP = d₂^VP` |
| (G₁₅) | def | `vertexSetC`: `selectedPart` (G₆) with `Sel = IsSetC` at `K = 7` and the counterterm record whose level-1 entries are the share. Plus `IsVertexSetCLimit` (the C₄ pattern) |
| (Sc₅) | def | `aSetC` = Barbieri–Remiddi (3), as `a1SixSetB` (C₅). Companions: enclosure (Sc₆), integral representation (Sc₇) `∫₀¹ λ⁽⁴⁾Δα = aSetC`. (Sc₆) and (Sc₇) are sealable at once from `QED/Chain/SetC*`, **but** (Sc₇) states `λ⁽⁴⁾` literally, so the BLP kernel enters a frozen statement as a definition. That is acceptable only as a *representation* goal. The headline must not mention it |
| (Sc₈) | meaning | family nonempty; order 7; loop count; disjoint from `IsVPChain 2`; embedding at trivial flavours |
| (Sc₉) | goal | integrability companion (the HC₀ pattern) |
| (HS₃) | goal | headline: (HC₃)'s binders and quantifier order, with Stage 2's graded data renormalized through `e²` (level 0) plus the share (G₁₄); conclusion `‖64π⁶F₂/e⁶ − aSetC‖ < η`; reported as a subset |
| (R-K₄) | optional anchor | a reusable statement of (S) at helper level (a named function `A_(c)(t)` as an explicit parametric integral). Freezing it would need a massive-photon object in a frozen model, which does not exist; recommend helper level only (D-54.3 asks for reusable objects, and a helper theorem suffices) |

Design questions for the author:
- (Q-c1) The share as a separate counterterm record (above) or a split theorem of the full level-1
  coefficients into family shares (needs every two-loop SE/vertex family; larger).
- (Q-c2) Whether the headline should instead be stated for set (c) + set (b) + set (a) together
  ("all VP-insertion sets"). The level-1 counterterm then needs splitting only between VP and
  non-VP parts.
- (Q-c3) The `kk` cancellation, as a family-level theorem or carried through the units.

## 4. Reuse for four loops

With the dispersion, every VP insertion into a two-loop vertex reduces to `∫ dσ(t) A(t)`. So the
kernel `A_(c)(t)` (single massive line) and its two-mass extension `A(t₁, t₂)` (the unit formulas
of section 2 already take two masses) cover eighth-order Group II (fourth-order vertex with VP
insertions, Kinoshita's classification as in AHKN), at no new kernel cost:
- `Π̂²` on one line (spectral weight `Im Π̂²`);
- Källén–Sabry on one line (`QED.Chain.ksRho` is in the repository);
- bubbles on both lines (`A(t₁,t₂)`);
- heavy-lepton bubbles (`ρ` at `M_f`). Set (c) with a muon or tau bubble is
  `A₂⁽⁶⁾(m_e/m_μ)`; the repository's `muon_chk.py` already checks BR74 (4) with this kernel.

Also reusable for four loops:
- the mixed-prescription two-loop `ε`-engine and the two-loop-outer nested-equals-joint Fubini
  (the same objects appear for Group II and for set (a)'s model link in reverse: two-loop VP
  inside a one-loop vertex);
- the VP-share counterterm mechanism (G₁₄), which at four loops becomes the shares of level-2
  coefficients.

Group III (the sixth-order vertex with a bubble) needs K⁽⁶⁾(t), which is not covered.

## 5. Risks

| # | Risk | Severity | Mitigation |
| --- | --- | --- | --- |
| K1 | Fibre densities per unit contain letters that cancel only in the sum (square roots from `Q(1−x) − x²` combined with `M_in`, `e`) | high | pilot the L pair first; compute per-unit spacelike densities numerically from `units*.py` and fit them (PSLQ against the alphabet of `F⁽⁴⁾` plus `x_Q`-letters) before any Lean |
| K2 | C and X fibres are 3D with two `x`-branches (`β = max(g, ex/(1−x))`) | high | as Phase 4's C and X (ξ-integration machinery exists); generator scripts as for `SetC*` |
| M1 | Mixed-prescription two-loop `ε`-limit | medium–high | treat `−iε_i` as complex masses with negative imaginary part in the parametric derivation; dominated convergence is unchanged |
| M2 | Three-loop nested = joint with a two-loop outer | high (the R2 analogue of set (b)) | inner-first route; power-count the margin first |
| M3 | Uniformity in `t` of the regulator limits | medium–high | the bound `C(1+ln t)/t` from the parametric form (largest `t`: `D ≥ βt`) |
| M4 | `kk` (longitudinal) parts do not vanish per graph, and the WT identity holds only at `ε → 0` | medium | carry `kk` as explicit extra unit pieces and prove that their sum vanishes at the parametric level, or prove a fixed-`ε` WT identity with vanishing remainders |
| M5 | VP-share counterterms: on-shell existence, `d₁^VP = d₂^VP`, integrability of share counterterm graphs under the block PV conditions (D-55 revised) | medium | the one-loop WI with a general photon mass, by dispersion |
| M6 | `M = M_in − te < 0` for `t > 4` in the outer-massive C and X | low | bounds through `M + βh > 0`; the masters are regular there |
| S1 | Size: 39 orbits; 8 placements × the Phase 4 limit proofs | medium | generalize the Phase 4 units to per-line masses **once**, with Phase 4 as a corollary, rather than copying |

## 6. File and effort estimates

Calibration: Phase 4 units L, X, S + C are ≈ 130 files and 37k lines (`QED/TwoLoop/Unit*`). Set (b)'s
model link is 83 files and 22k lines (`QED/ChainProof`); its value side is 33 files and 11k lines
(`QED/Chain`).

| Stage | Content | Files |
| --- | --- | --- |
| K1 | numerics: per-unit spacelike densities, PSLQ, generator scripts | (scripts) |
| K2 | L-pair pilot: fibre density in closed form, (S) restricted to the L pair | 8–15 |
| K3 | S, C, X pairs; assembly of (S); `|A| ≤ C(1+ln t)/t` | 50–90 |
| K4 | `a_(c) = ∫ρ A = aSetC` (Fubini, `piHat_eq_spectral`) | 2–4 |
| L1 | two-mass generalization of the Phase 4 unit chain (class data, `openZero`, hierarchical reductions), Phase 4 recovered as a corollary | 30–60 |
| L2 | regulator limits with the massive line, uniform in `t` | 40–80 |
| M1 | packet Stage 3c (drafting, two reviews, freeze) | ~13 frozen files |
| M2 | enumeration (`IsSetC` ⇔ 39 orbits), meaning theorems | 10–20 |
| M3 | integrability (HC₀ analogue) | 10–20 |
| M4 | nested = joint, mixed-prescription `ε`-engine at two loops, `kk` cancellation | 40–70 |
| M5 | covariance, mirror, `q → 0`, share counterterms, assembly | 25–45 |

Totals: Stage K 60–110 files; Stage L 70–140; Stage M 85–155. Overall 215–405.

## 7. Files in this directory

- `blp.py`: BLP kernel; check 1; the Stieltjes side of (S).
- `gen.py` → `units.pkl`: b-integrated hierarchical integrands of L, S₊, C₊, X with separate
  photon masses, from the repository engine.
- `units2d.py`, `units2dfix.py`: L and S at `(μ, ν)` (adaptive and fixed tanh-sinh rules).
- `units3d.py`, `run3d.sh` → `run3d_*.out`: C and X at `(μ, ν)`.
- `run2d.py` → `run2d.out`, `run2d.json`: the 2D pieces and `∫λ⁽⁴⁾Q/(Q+t)` at `t = 1, 4`.
- `irtest.py`: the IR cancellation in S(0,t) + C(0,t).
- `assemble.py`: the check-2 table.
