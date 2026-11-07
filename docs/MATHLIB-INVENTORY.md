# Mathlib inventory

- **Mathlib commit:** `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0`;
  the checkout's `lean-toolchain` reads `leanprover/lean4:v4.35.0`)
- **Inspected path:** `/home/scott/KAM-dev/.lake/packages/mathlib` (read-only; commit
  confirmed with `git rev-parse HEAD`)
- **Date:** 2026-11-07
- **Scope:** This is a search inventory made with grep, ripgrep and file reads only. No
  Lean build or proof checking was done.
- **Lean confirmation (orchestrator, 2026-11-07):** in the pinned QED-dev environment,
  a transient untracked module importing the three focused import sets below elaborated
  `#check` for 26 sampled names from sections 1–6. They were `CliffordAlgebra.lift`,
  `QuadraticMap.weightedSumSquares`, `LieAlgebra.Orthogonal.indefiniteDiagonal`,
  `MeasureTheory.integral_add_right_eq_self`, `MeasureTheory.integral_neg_eq_self`,
  `MeasureTheory.integral_fun_norm_addHaar`, `integrable_rpow_neg_one_add_norm_sq`,
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `DifferentiableOn.analyticOnNhd`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, `Complex.starConvex_slitPlane`,
  `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`, `PowerSeries.trunc`, and
  others. All imports loaded from the cached build; nothing was rebuilt. The remaining
  names are grep-verified only.

Context: [Campaign HQ](../README.md) · [Project outline](PROJECT-OUTLINE.md) ·
[What "proved" means](WHAT-IS-PROVED.md) · [Orchestrator launch](ORCHESTRATOR-LAUNCH.md) ·
[Conventions](CONVENTIONS.md) · [Regularization](REGULARIZATION.md)

## How to read this

- **Names** are fully qualified Lean names. Each one was found by a script that walks
  `namespace`/`section`/`end` blocks (skipping comments) in that checkout. Locations are
  `path:line` relative to the Mathlib root and point to the declaration keyword.
- **Status:** AVAILABLE means the named declaration exists and does the job. PARTIAL
  means some pieces exist and something specific is missing. MISSING means the search
  found nothing; the search terms are listed.
- **Generated names.** Some names are created by `@[to_additive]` and never appear
  literally in the source. For these, the table gives the multiplicative source
  declaration and a place where Mathlib uses the additive name.
- **Not checked:** exact elaboration behavior, implicit arguments, and instance
  availability for `ℂ`. Lean must check these before any proof relies on a name.
- **Module system.** Mathlib at this commit uses the Lean module system (`module`,
  `public import`). `Mathlib.Data.Complex.Basic` is now a `deprecated_module`
  (since 2026-08-27) that forwards to `Mathlib.Basic.Complex.Basic`.

Summary counts (rows in the tables below): **AVAILABLE 44 · PARTIAL 8 · MISSING 9**.

## 1. Finite-dimensional linear algebra, Clifford algebras, quadratic forms

| # | Item | Status | Evidence (`name` — `path:line`) and notes |
|---|---|---|---|
| 1.1 | `Matrix (Fin 4) (Fin 4) ℂ`, literals | AVAILABLE | `Matrix` — `Mathlib/LinearAlgebra/Matrix/Defs.lean:56` (`def Matrix (m n α)`); `Matrix.of` — `Mathlib/LinearAlgebra/Matrix/Defs.lean:91`; `!![…]` syntax — `Mathlib/LinearAlgebra/Matrix/Notation.lean:97`. |
| 1.2 | Trace | AVAILABLE | `Matrix.trace` — `Mathlib/LinearAlgebra/Matrix/Trace.lean:43`; `Matrix.trace_mul_comm` — `…/Trace.lean:156` (tr(AB)=tr(BA)); `Matrix.trace_mul_cycle` — `…/Trace.lean:159`; `Matrix.trace_one` — `…/Trace.lean:144` (= card n). |
| 1.3 | Conjugate transpose, star | AVAILABLE | `Matrix.conjTranspose` — `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:43`; `Matrix.conjTranspose_mul` — `…/ConjTranspose.lean:349`; `Matrix.star_eq_conjTranspose` — `…/ConjTranspose.lean:420`; anonymous `instance … : StarRing (Matrix n n α)` — `…/ConjTranspose.lean:438`; `Matrix.trace_conjTranspose` — `Mathlib/LinearAlgebra/Matrix/Trace.lean:75`; `Matrix.IsHermitian` — `Mathlib/LinearAlgebra/Matrix/Hermitian.lean:45`; `Matrix.unitaryGroup` — `Mathlib/LinearAlgebra/UnitaryGroup.lean:105`. |
| 1.4 | Kronecker products | AVAILABLE | `Matrix.kroneckerMap` — `Mathlib/LinearAlgebra/Matrix/Kronecker.lean:55`; `Matrix.kronecker` — `…/Kronecker.lean:274`; notation `⊗ₖ` (`scoped[Kronecker]`) — `…/Kronecker.lean:278`; `Matrix.mul_kronecker_mul` — `…/Kronecker.lean:382` (mixed product); `Matrix.trace_kronecker` — `…/Kronecker.lean:398`; `Matrix.conjTranspose_kronecker` — `…/Kronecker.lean:408`; `Matrix.one_kronecker_one` — `…/Kronecker.lean:368`. |
| 1.5 | Block matrices | AVAILABLE | `Matrix.fromBlocks` — `Mathlib/Data/Matrix/Block.lean:45`; `Matrix.fromBlocks_multiply` — `…/Block.lean:213`; `Matrix.fromBlocks_conjTranspose` — `…/Block.lean:138`; `Matrix.fromBlocks_diagonal` — `…/Block.lean:266`; `Matrix.fromBlocks_one` — `…/Block.lean:298`. There is no trace-of-blocks lemma (searched `trace.*fromBlocks`). |
| 1.6 | Pauli matrices | MISSING | Searched `pauli` (case-insensitive). The only hits are the author name "Paulino". |
| 1.7 | `indefiniteDiagonal`, `so'` | AVAILABLE | Not `Matrix.indefiniteDiagonal`. The real name is `LieAlgebra.Orthogonal.indefiniteDiagonal` — `Mathlib/Algebra/Lie/Classical.lean:175`, a matrix on `p ⊕ q` with diagonal +1 on p and −1 on q. Also `LieAlgebra.Orthogonal.so'` — `…/Classical.lean:180` (skew-adjoint matrices for that form, i.e. 𝔰𝔬(p,q) as a `LieSubalgebra`); `LieAlgebra.Orthogonal.so` — `…/Classical.lean:166`; `LieAlgebra.Orthogonal.Pso` — `…/Classical.lean:185`; `LieAlgebra.Orthogonal.indefiniteDiagonal_transform` — `…/Classical.lean:208`; `LieAlgebra.Orthogonal.soIndefiniteEquiv` — `…/Classical.lean:224` (𝔰𝔬(p,q) ≃ 𝔰𝔬(p+q) when some i has i² = −1). |
| 1.8 | Indefinite orthogonal / Lorentz group | MISSING | Only the definite `Matrix.orthogonalGroup` — `Mathlib/LinearAlgebra/UnitaryGroup.lean:318`. Searched `orthogonalGroup`, `OrthogonalGroup`, `lorentz`, `indefinite`. |
| 1.9 | Clifford algebra | AVAILABLE | `CliffordAlgebra` — `Mathlib/LinearAlgebra/CliffordAlgebra/Basic.lean:71`; `CliffordAlgebra.ι` — `…/Basic.lean:111`; `CliffordAlgebra.ι_sq_scalar` — `…/Basic.lean:119` (ι m · ι m = Q m); `CliffordAlgebra.lift` — `…/Basic.lean:136`, an equivalence between linear maps `f` with `f m * f m = algebraMap (Q m)` and algebra maps `CliffordAlgebra Q →ₐ A`; `CliffordAlgebra.lift_ι_apply` — `…/Basic.lean:165`; `CliffordAlgebra.ι_mul_ι_add_swap` — `…/Basic.lean:263` (anticommutator = `polar Q a b`); `CliffordAlgebra.induction` — `…/Basic.lean:196`; `CliffordAlgebra.equivOfIsometry` — `…/Basic.lean:379`; `CliffordAlgebra.equivBaseChange` — `…/CliffordAlgebra/BaseChange.lean:182`; `CliffordAlgebra.reverse` — `…/Conjugation.lean:97`; `CliffordAlgebra.involute` — `…/Conjugation.lean:46`; `CliffordAlgebra.equivExterior` — `…/Contraction.lean:351`; `CliffordAlgebraComplex.equiv` — `…/Equivs.lean:188`; `CliffordAlgebraQuaternion.equiv` — `…/Equivs.lean:317`. |
| 1.10 | Spin groups, spinors | PARTIAL | `spinGroup` — `Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup.lean:293` and `pinGroup` — `…/SpinGroup.lean:154`, both as submonoids of the Clifford algebra. No spinor modules or representations: searched `spinor`. |
| 1.11 | Quadratic and bilinear forms | AVAILABLE | `QuadraticMap` — `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:146`; `QuadraticMap.weightedSumSquares` — `…/QuadraticForm/Basic.lean:1410` (`QuadraticMap R (ι → R) R` with weights w); `QuadraticMap.weightedSumSquares_apply` — `…/Basic.lean:1417`; `QuadraticMap.polar` — `…/Basic.lean:96`; `QuadraticMap.polarBilin` — `…/Basic.lean:317`; `QuadraticMap.associated` — `…/Basic.lean:962`; `QuadraticForm.toMatrix'` — `…/Basic.lean:1170`; `Matrix.toBilin'` — `Mathlib/LinearAlgebra/Matrix/BilinearForm.lean:93`; `LinearMap.BilinForm` — `Mathlib/LinearAlgebra/BilinearMap.lean:529`; `QuadraticMap.IsometryEquiv` — `…/QuadraticForm/IsometryEquiv.lean:39`; `QuadraticMap.Equivalent` — `…/IsometryEquiv.lean:46`; Sylvester existence `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared` — `…/QuadraticForm/Real.lean:87`; `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` — `…/QuadraticForm/AlgClosed.lean:49`; signature `sigPos` — `…/QuadraticForm/Signature.lean:65`. The file's docstring calls it `QuadraticForm.sigPos`, but the source declares it outside any namespace. |
| 1.12 | Minkowski metric / spacetime | MISSING | Searched `minkowski` (hits are only the Minkowski inequality, bound, and convexity results), `spacetime`, `space-time`, `relativ`, `lorentz`. The nearest substitute is `QuadraticMap.weightedSumSquares` with weights (1,−1,−1,−1). |
| 1.13 | Dirac gamma matrices | MISSING | Searched `gamma matri`, `gammaMatri`, `clifford relation`, `dirac` (hits are only Dirac measures), `spinor`. |

## 2. Lebesgue/Bochner integration on ℝⁿ

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 2.1 | `EuclideanSpace ℝ (Fin n)` vs `Fin n → ℝ` volume | AVAILABLE | `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp` — `Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean:124`; `PiLp.volume_preserving_ofLp` — `…/InnerProductSpace.lean:134`; `PiLp.volume_preserving_toLp` — `…/InnerProductSpace.lean:139`; `WithLp.volume_preserving_ofLp` — `…/InnerProductSpace.lean:206` (for `WithLp 2 (U × V)`). There is no `EuclideanSpace.volume_preserving_measurableEquiv` at this commit. |
| 2.2 | Split ℝ⁴ = ℝ × ℝ³ | AVAILABLE | `MeasurableEquiv.piFinSuccAbove` — `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:566`; `MeasureTheory.measurePreserving_piFinSuccAbove` — `Mathlib/MeasureTheory/Constructions/Pi.lean:807`; `MeasureTheory.volume_preserving_piFinSuccAbove` — `…/Constructions/Pi.lean:819`. These are stated for pi types. For `EuclideanSpace`, compose with 2.1, or use `PiLp.sumPiLpEquivProdLpPiLp` — `Mathlib/Analysis/Normed/Lp/PiLp.lean:1028` (a linear isometry) together with `LinearIsometryEquiv.measurePreserving`. |
| 2.3 | Fubini/Tonelli | AVAILABLE | `MeasureTheory.integral_prod` — `Mathlib/MeasureTheory/Integral/Prod.lean:443`; `MeasureTheory.integral_prod_symm` — `…/Integral/Prod.lean:466`; `MeasureTheory.integral_integral_swap` — `…/Integral/Prod.lean:481`; `MeasureTheory.integrable_prod_iff` — `…/Integral/Prod.lean:230`; `MeasureTheory.lintegral_prod` — `Mathlib/MeasureTheory/Measure/Prod.lean:1033`. |
| 2.4 | Translation invariance | AVAILABLE | `MeasureTheory.integral_add_right_eq_self`, `…integral_add_left_eq_self`, `…integral_sub_right_eq_self` and `…integral_neg_eq_self` are generated by `@[to_additive]` from `MeasureTheory.integral_mul_right_eq_self` — `Mathlib/MeasureTheory/Group/Integral.lean:101`, `MeasureTheory.integral_mul_left_eq_self` — `…:91`, `MeasureTheory.integral_div_right_eq_self` — `…:108` and `MeasureTheory.integral_inv_eq_self` — `…:40`. Mathlib uses the additive names, for example in `Mathlib/Analysis/Calculus/Rademacher.lean:191`. |
| 2.5 | Linear change of variables | AVAILABLE | `MeasureTheory.Measure.integral_comp_smul` — `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:92`; `MeasureTheory.Measure.integral_comp_mul_left` — `…/NormedSpace.lean:152`; `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` — `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:231` (pushforward = abs(det)⁻¹ · μ); `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` — `Mathlib/MeasureTheory/Function/Jacobian.lean:1213` (general Jacobian formula); `LinearIsometryEquiv.measurePreserving` — `…/Haar/InnerProductSpace.lean:151`; `MeasureTheory.integral_comp` — `…/Haar/NormedSpace.lean:234` (for `f : E ≃ₗᵢ[ℝ] F`). |
| 2.6 | Radial integration in ℝⁿ | AVAILABLE | `MeasureTheory.integral_fun_norm_addHaar` — `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:297`: `∫ x, f ‖x‖ ∂μ = dim E • μ.real (ball 0 1) • ∫ y in Ioi 0, y ^ (dim E - 1) • f y`. Also `MeasureTheory.integrable_fun_norm_addHaar` — `…:256` (an iff); `MeasureTheory.Measure.toSphere` — `…:52`; `MeasureTheory.Measure.toSphere_apply_univ` — `…:88` (sphere measure = dim · vol(ball)); `MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` — `…:143`. |
| 2.7 | Polar coordinates in ℝ² | AVAILABLE | `integral_comp_polarCoord_symm` — `Mathlib/Analysis/SpecialFunctions/PolarCoord.lean:139`. It is in the root namespace, not `MeasureTheory.`. There are no n-dimensional spherical angle coordinates, but 2.6 makes them unnecessary. |
| 2.8 | Volumes of balls | AVAILABLE | `EuclideanSpace.volume_ball` — `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:308` (Gamma-function formula); `InnerProductSpace.volume_ball` — `…:344`; `InnerProductSpace.volume_ball_of_dim_even` — `…:360` (gives πᵏ/k!, so π²/2 for the unit ball in dimension 4); `MeasureTheory.Measure.addHaar_ball` — `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:456`. |
| 2.9 | Integrability of (1+‖x‖²)^(−s) | AVAILABLE | `integrable_rpow_neg_one_add_norm_sq` — `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean:145` (integrable when `finrank < r`, exponent `-r/2`); `integrable_one_add_norm` — `…:135`; `finite_integral_one_add_norm` — `…:96`. |
| 2.10 | Simplex / Dirichlet integrals | MISSING | Searched `integral.*simplex`, `simplex.*integral`, `volume.*stdSimplex`, `dirichlet.?integral`, `feynman`. Only the set exists: `stdSimplex` — `Mathlib/Analysis/Convex/StdSimplex.lean:40`, with `convex_stdSimplex` — `…:49` and `isCompact_stdSimplex` — `…:218`. |
| 2.11 | Interval integrals, FTC, improper integrals | AVAILABLE | `intervalIntegral.integral_eq_sub_of_hasDerivAt` — `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1148`; `intervalIntegral.integral_hasDerivAt_right` — `…/FundThmCalculus.lean:725`; `intervalIntegral.integral_comp_mul_deriv` — `…/IntervalIntegral/IntegrationByParts.lean:512` (substitution); `intervalIntegral.integral_mul_deriv_eq_deriv_mul` — `…/IntegrationByParts.lean:141` (integration by parts); `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` — `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:786`; `MeasureTheory.integral_of_hasDerivAt_of_tendsto` — `…:1054`; `MeasureTheory.intervalIntegral_tendsto_integral_Ioi` — `…:658`; `MeasureTheory.integral_comp_rpow_Ioi` — `…:1125`; `MeasureTheory.integral_comp_mul_left_Ioi` — `…:1205`. |

## 3. Special functions and closed-form integrals

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 3.1 | Gamma | AVAILABLE | `Real.Gamma` — `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:402`; `Complex.Gamma` — `…/Gamma/Basic.lean:287`; `Real.Gamma_eq_integral` — `…:405`; `Complex.Gamma_eq_integral` — `…:319` (Re s > 0); `Real.Gamma_add_one` — `…:410`; `Real.Gamma_nat_eq_factorial` — `…:422`; `Real.Gamma_one_half_eq` — `…/Gaussian/GaussianIntegral.lean:306`; `Complex.differentiableAt_Gamma` — `…/Gamma/Deriv.lean:75`; `Complex.Gamma_ne_zero` — `…/Gamma/Beta.lean:427`. |
| 3.2 | Beta, Gamma–Beta relation | AVAILABLE | `Complex.betaIntegral` — `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:60` (∫₀¹ x^(u−1)(1−x)^(v−1)); `Complex.betaIntegral_convergent` — `…:78`; `Complex.Gamma_mul_Gamma_eq_betaIntegral` — `…:124`; `Complex.betaIntegral_eq_Gamma_mul_div` — `…:537`; `Complex.betaIntegral_recurrence` — `…:142`. On the real side there is only `ProbabilityTheory.beta` — `Mathlib/Probability/Distributions/Beta.lean:33` (defined as ΓΓ/Γ) with `ProbabilityTheory.beta_eq_betaIntegralReal` — `…:41`. There is no `Real.Beta`. |
| 3.3 | Gamma-type integrals ∫₀^∞ t^(a−1)e^(−rt) | AVAILABLE | `Real.integral_rpow_mul_exp_neg_mul_Ioi` — `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:465` (= (1/r)^a Γ(a)); `Complex.integral_cpow_mul_exp_neg_mul_Ioi` — `…:372` (complex a, real r > 0). |
| 3.4 | Gaussian integrals (real, complex with Re > 0, ℝⁿ) | AVAILABLE | `integral_gaussian` — `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:210`; `integral_gaussian_complex` — `…:236`; `integral_gaussian_Ioi` — `…:289`; `integrable_cexp_neg_mul_sq` — `…:142`; `integral_cexp_quadratic` — `…/Gaussian/FourierTransform.lean:174`; `fourierIntegral_gaussian` — `…/FourierTransform.lean:201`; `GaussianFourier.integral_rexp_neg_mul_sq_norm` — `…:330` and `GaussianFourier.integral_cexp_neg_mul_sq_norm` — `…:325` (on a finite-dimensional inner product space, = (π/b)^(dim/2)); `GaussianFourier.integral_cexp_neg_mul_sq_norm_add` — `…:316`; `GaussianFourier.integral_cexp_neg_sum_mul_add` — `…:277` (diagonal coefficients on `ι → ℝ`). |
| 3.5 | ∫_ℝ (t²+a)^(−n) | PARTIAL | Only n = 1: `integral_univ_inv_one_add_sq` — `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean:292` (= π); `integral_Ioi_inv_one_add_sq` — `…:286`; `integral_inv_sq_add_sq` — `…/Integrals/Basic.lean:354` (on an interval, via arctan); `integral_mul_rpow_one_add_sq` — `…/Integrals/Basic.lean:436` (the odd integrand x(1+x²)^t). General n, or a real exponent over ℝ, is missing. Searched `one_add_sq`, `add_sq_rpow`, `sq_add_rpow`. |
| 3.6 | arctan | AVAILABLE | `Real.hasDerivAt_arctan` — `Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean:82`; `integral_inv_one_add_sq` — `…/Integrals/Basic.lean:350`; `Real.tendsto_arctan_atTop` — `…/Trigonometric/Arctan.lean:189`. |
| 3.7 | log and power integrals | AVAILABLE | `integral_log` — `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:303`; `integral_log_from_zero` — `…:292`; `integral_id_div_sq_add_sq` — `…:370` (gives a log); `Real.hasDerivAt_log` — `…/Log/Deriv.lean:53`; `integral_rpow` — `…/Integrals/Basic.lean:147`; `integral_Ioi_rpow_of_lt` — `…/ImproperIntegrals.lean:178`; `integrableOn_Ioi_rpow_iff` — `…/ImproperIntegrals.lean:134`. |

## 4. Parametric integrals

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 4.1 | Dominated convergence | AVAILABLE | `MeasureTheory.tendsto_integral_of_dominated_convergence` — `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:58`; `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` — `…:68` (countably generated filters, so it covers `𝓝[>] 0`). |
| 4.2 | Continuity of parameter integrals | AVAILABLE | `MeasureTheory.continuous_of_dominated` — `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:476`; `MeasureTheory.continuousAt_of_dominated` — `…:458`; `MeasureTheory.continuousOn_of_dominated` — `…:467`; `continuous_parametric_integral_of_continuous` — `…/Bochner/Set.lean:1123`; `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` — `…/DominatedConvergence.lean:614`. |
| 4.3 | Differentiation under the integral | AVAILABLE | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` — `Mathlib/Analysis/Calculus/ParametricIntegral.lean:284`. Its scalar field is `𝕜` with `[RCLike 𝕜]`, so `𝕜 = ℂ` is allowed. Also `hasFDerivAt_integral_of_dominated_of_fderiv_le` — `…:206`; `hasFDerivAt_integral_of_dominated_loc_of_lip` — `…:161`; `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` — `…/ParametricIntervalIntegral.lean:96`. |
| 4.4 | Holomorphy of parameter integrals in a complex parameter | PARTIAL | There is no packaged theorem that a holomorphic, locally dominated integrand gives a holomorphic `DifferentiableOn ℂ`/`AnalyticOnNhd ℂ` integral. Searched lemma names that combine integral with analytic/holomorph/differentiableOn, and statements containing both `DifferentiableOn ℂ`/`AnalyticOnNhd ℂ` and `∫`. Route: 4.3 with 𝕜 = ℂ at each point, then `DifferentiableOn.analyticOnNhd` — `Mathlib/Analysis/Complex/CauchyIntegral.lean:706` or `Complex.analyticOnNhd_iff_differentiableOn` — `…:747`. A worked precedent is `mellin_differentiableAt_of_isBigO_rpow` — `Mathlib/Analysis/MellinTransform.lean:401`. Alternatives: `TendstoLocallyUniformlyOn.differentiableOn` — `…/Complex/LocallyUniformLimit.lean:136`, or Morera via `Complex.IsConservativeOn.isExactOn_ball` — `…/Complex/HasPrimitives.lean:276` and `Complex.IsExactOn.differentiableOn` — `…:139`. |

## 5. Complex analysis

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 5.1 | Cauchy theorem on rectangles | AVAILABLE | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` — `Mathlib/Analysis/Complex/CauchyIntegral.lean:292`; `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` — `…:263`; `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` — `…:279`. |
| 5.2 | Circle and curve integrals, Cauchy formula | AVAILABLE | `circleIntegral` — `Mathlib/MeasureTheory/Integral/CircleIntegral.lean:434`; `circleIntegral.integral_sub_center_inv` — `…:580`; `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` — `Mathlib/Analysis/Complex/CauchyIntegral.lean:529`; `DifferentiableOn.circleIntegral_sub_inv_smul` — `…:560`; `curveIntegral` — `Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:124` (1-forms along a `Path`). |
| 5.3 | Residue theorem | MISSING | Searched `residue`. The only hits are algebraic (residue fields, residue classes). |
| 5.4 | Ray/sector contours, Wick rotation | MISSING | Searched `wick`, `contour integral`, `sector`, `ray.*integral`. The closest pattern is a vertical-line contour shift: `GaussianFourier.verticalIntegral` — `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean:50`, `GaussianFourier.tendsto_verticalIntegral` — `…:107` and `GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I` — `…:134`. These combine the rectangle theorem with vertical sides that vanish in the limit. |
| 5.5 | Identity theorem | AVAILABLE | `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` — `Mathlib/Analysis/Analytic/IsolatedZeros.lean:238`; `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` — `…:214`; `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` — `Mathlib/Analysis/Analytic/Uniqueness.lean:224`. |
| 5.6 | Principal-branch log and cpow | AVAILABLE | `Complex.log` — `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:30`; `Complex.cpow` — `…/Pow/Complex.lean:27`; `Complex.cpow_def` — `…/Pow/Complex.lean:37`; `Complex.hasDerivAt_log` — `…/Complex/LogDeriv.lean:37`; `Complex.differentiableAt_log` — `…/LogDeriv.lean:41`; `continuousAt_clog` — `…/Complex/Log.lean:249` (root namespace); `analyticAt_clog` — `…/Complex/Analytic.lean:28` (root namespace); `AnalyticAt.cpow` — `…/Complex/Analytic.lean:65`; `DifferentiableAt.cpow` — `…/Pow/Deriv.lean:106`; `DifferentiableOn.cpow_const` — `…/Pow/Deriv.lean:148`; `HasDerivAt.cpow_const` — `…/Pow/Deriv.lean:209`; `Complex.ofReal_cpow` — `…/Pow/Real.lean:282`; `Complex.mul_cpow_ofReal_nonneg` — `…/Pow/Complex.lean:189`. Paths are under `Mathlib/Analysis/SpecialFunctions/`. |
| 5.7 | Slit plane and its connectedness | PARTIAL | `Complex.slitPlane` — `Mathlib/Analysis/Complex/Basic.lean:628` ({0 < re ∨ im ≠ 0}); `Complex.isOpen_slitPlane` — `…:644`; `Complex.mem_slitPlane_iff` — `…:630`; `Complex.starConvex_slitPlane` — `Mathlib/Analysis/Complex/Convex.lean:37`; `StarConvex.isPathConnected` — `Mathlib/Analysis/Convex/PathConnected.lean:79`; `Convex.isPreconnected` — `…:94`. There is no lemma named `isConnected_slitPlane` or `isPreconnected_slitPlane` (searched), though connectedness follows in two steps from star-convexity. Cut planes in a mass parameter, such as ℂ \ (−∞, −m²], need project lemmas. |

## 6. Formal power series

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 6.1 | `PowerSeries` core | AVAILABLE | `PowerSeries` — `Mathlib/RingTheory/PowerSeries/Basic.lean:57`; `PowerSeries.coeff` — `…:77`; `PowerSeries.X` — `…:155`; `PowerSeries.coeff_mul` — `…:246`; `PowerSeries.ext` — `…:94`; `PowerSeries.subst` — `…/PowerSeries/Substitution.lean:158`. |
| 6.2 | Truncation, polynomials as truncations | AVAILABLE | `PowerSeries.trunc` — `Mathlib/RingTheory/PowerSeries/Trunc.lean:51` (`trunc n : R⟦X⟧ →ₗ[R] R[X]`, keeps degrees < n); `PowerSeries.coeff_trunc` — `…:63`; `PowerSeries.trunc_trunc_mul_trunc` — `…:192`; `PowerSeries.trunc_coe_eq_self` — `…:205`; `Polynomial.coeff_coe` — `…/PowerSeries/Basic.lean:782`; `Polynomial.coeToPowerSeries.ringHom` — `…/PowerSeries/Basic.lean:853`. |
| 6.3 | `MvPowerSeries` | AVAILABLE | `MvPowerSeries` — `Mathlib/RingTheory/MvPowerSeries/Basic.lean:86`; `MvPowerSeries.coeff` — `…:137`; `MvPowerSeries.trunc` — `Mathlib/RingTheory/MvPowerSeries/Trunc.lean:185`. |
| 6.4 | Quotient by (X^(N+1)) | PARTIAL | There is no dedicated quotient or truncated-ring API. Searched `span {X ^` in the PowerSeries, MvPowerSeries and Polynomial folders, and `truncated` in RingTheory (hits are only Witt vectors). `PowerSeries.X_pow_dvd_iff` — `Mathlib/RingTheory/PowerSeries/Basic.lean:513` describes the ideal, and the generic `Ideal.Quotient` applies. |
| 6.5 | Link between analytic expansions and `PowerSeries` | PARTIAL | `HasFPowerSeriesAt` — `Mathlib/Analysis/Analytic/Basic.lean:95`; `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` — `…:771`; `FormalMultilinearSeries.ofScalars` — `Mathlib/Analysis/Analytic/OfScalars.lean:38`. No bridge to `PowerSeries` coefficients: searched `PowerSeries` under `Mathlib/Analysis`, excluding the `FPowerSeries`/`FormalMultilinear` names. |

## 7. Distributions and Fourier analysis

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 7.1 | Schwartz space | AVAILABLE | `SchwartzMap` — `Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:75`. |
| 7.2 | Tempered distributions | AVAILABLE | `TemperedDistribution` — `Mathlib/Analysis/Distribution/TemperedDistribution.lean:53` (`abbrev … := 𝓢(E, ℂ) →Lₚₜ[ℂ] F`); `TemperedDistribution.instFourierTransform` — `…:469`; `Distribution` — `Mathlib/Analysis/Distribution/Distribution.lean:166`. |
| 7.3 | Fourier transform | AVAILABLE | `Real.fourierIntegral` does **not** exist at this commit. Use the `𝓕` notation through `Real.instFourierTransform` — `Mathlib/Analysis/Fourier/FourierTransform.lean:428` and `Real.fourier_eq` — `…:434`. Also `VectorFourier.fourierIntegral` — `…:81`; class `FourierTransform` — `Mathlib/Analysis/Fourier/Notation.lean:34`; `SchwartzMap.fourierTransformCLM` — `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean:53`. |
| 7.4 | Fourier inversion | AVAILABLE | `MeasureTheory.Integrable.fourierInv_fourier_eq` — `Mathlib/Analysis/Fourier/Inversion.lean:166`; `Continuous.fourierInv_fourier_eq` — `…:175`; `SchwartzMap.instFourierPair` — `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean:130`. |

## 8. Fermionic and combinatorial structures

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 8.1 | Exterior algebra | AVAILABLE | `ExteriorAlgebra` — `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean:60`; `ExteriorAlgebra.ι` — `…:69`; `ExteriorAlgebra.ι_sq_zero` — `…:90`; `ExteriorAlgebra.ι_add_mul_swap` — `…:247`; `ExteriorAlgebra.ιMulti` — `…:271`; `ExteriorAlgebra.lift` — `…:109`. |
| 8.2 | Grassmann / supercommutative algebras | PARTIAL | `GradedTensorProduct` — `Mathlib/LinearAlgebra/TensorProduct/Graded/Internal.lean:73` (graded tensor product with Koszul signs). No superalgebra or supercommutative class: searched `supercommut`, `super-commut`, `superalgebra`, `grassmann` (hits are only Grassmannian varieties). |
| 8.3 | Permutation signs | AVAILABLE | `Equiv.Perm.sign` — `Mathlib/GroupTheory/Perm/Sign.lean:358`; `Equiv.Perm.sign_swap` — `…:389`; `Matrix.det_apply` — `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:66`; `MultilinearMap.alternatization` — `Mathlib/LinearAlgebra/Alternating/Basic.lean:842`. |
| 8.4 | Pairings, Pfaffians, hafnians, Wick/Isserlis | MISSING | Searched `pfaffian`, `hafnian`, `wick`, `isserlis`, `perfectMatching`, `pairings`. Related pieces: `SimpleGraph.Subgraph.IsPerfectMatching` — `Mathlib/Combinatorics/SimpleGraph/Matching.lean:236`; `Nat.doubleFactorial` — `Mathlib/Data/Nat/Factorial/DoubleFactorial.lean:32`; `Finset.prod_involution` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:697`. |

## 9. Asymptotics and limits

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 9.1 | Big-O / little-o | AVAILABLE | `Asymptotics.IsBigO` — `Mathlib/Analysis/Asymptotics/Defs.lean:85`; `Asymptotics.IsLittleO` — `…:169`; `Asymptotics.isBigO_iff` — `…:96`; `Asymptotics.IsBigO.trans` — `…/Asymptotics/Basic.lean:288`; `Asymptotics.IsBigO.mul` — `…/Asymptotics/Ring.lean:151`; `Asymptotics.isLittleO_pow_pow` — `…/Asymptotics/Lemmas.lean:583`; `Asymptotics.IsEquivalent` — `…/Asymptotics/AsymptoticEquivalent.lean:77`. |
| 9.2 | Limits along `nhdsWithin 0 (Set.Ioi 0)` | AVAILABLE | Notation `𝓝[>] x` (`scoped[Topology]`, unfolds to `nhdsWithin x (Set.Ioi x)`) — `Mathlib/Topology/Defs/Filter.lean:155`; `Filter.Tendsto` — `Mathlib/Order/Filter/Defs.lean:421`; `tendsto_nhdsWithin_iff` — `Mathlib/Topology/NhdsWithin.lean:474`; `tendsto_nhdsWithin_of_tendsto_nhds` — `…:398`; `tendsto_log_mul_rpow_nhdsGT_zero` — `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:398`. |
| 9.3 | Iterated limits | PARTIAL | `TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto` — `Mathlib/Topology/UniformSpace/UniformConvergence.lean:612` (Moore–Osgood-style interchange). There is no general double-limit API beyond product filters. Searched `moore`, `iterated limit`, `swap.*lim`, `interchange.*limit`. |

## 10. Numerics

| # | Item | Status | Evidence and notes |
|---|---|---|---|
| 10.1 | Bounds on π and constants | AVAILABLE | `Real.pi_gt_three` — `Mathlib/Analysis/Real/Pi/Bounds.lean:151`; `Real.pi_gt_d6` — `…:178`; `Real.pi_lt_d6` — `…:184`; `Real.pi_gt_d20` — `…:190`; `Real.pi_lt_d20` — `…:206`; `Real.pi_pos` — `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:158`; `Real.log_two_near_10` — `Mathlib/Analysis/Complex/ExponentialBounds.lean:71`; `Real.exp_one_gt_d9` — `…:35`. |
| 10.2 | `norm_num` and matrix simprocs | AVAILABLE | `norm_num` extensions in `Mathlib/Tactic/NormNum/` (for example `RealSqrt.lean`, `Pow.lean`); the `norm_matmul` simproc — `Mathlib/Tactic/NormMatMul.lean:70` (products of `!![…]` literals over `Fin`, used via `simp only`); the `norm_det` simproc — `Mathlib/Tactic/NormDet.lean:68`. |
| 10.3 | Verified interval arithmetic | MISSING | Searched `interval arithmetic`. The only hit is `Mathlib/Algebra/Order/Interval/Basic.lean`, the algebra of order intervals, which is not a numerics tactic. |

## Missing mathematics for the one-loop pilot

| Must build | Closest Mathlib building blocks |
|---|---|
| Minkowski bilinear form g = diag(−1,+1,+1,+1) on ℝ⁴/ℂ⁴ (the mostly-plus convention of decision D-7; see [CONVENTIONS.md](CONVENTIONS.md)) | `QuadraticMap.weightedSumSquares` (1.11), `QuadraticMap.polarBilin`, `LieAlgebra.Orthogonal.indefiniteDiagonal` (1.7), `Matrix.toBilin'` |
| Weyl-representation gamma matrices in `Matrix (Fin 4) (Fin 4) ℂ` with proved {γ^μ, γ^ν} = −2g^{μν}·1 (source (36.9)), β = γ⁰ Hermitian, βγ^μβ = (γ^μ)ᴴ, S^{μν} = (i/4)[γ^μ, γ^ν]; γ⁵ is not needed for the pilot | Literals plus `norm_matmul` (10.2); `Matrix.kronecker`/`Matrix.mul_kronecker_mul` or `Matrix.fromBlocks_multiply` for Pauli-based construction; `CliffordAlgebra.lift` turns the Clifford relation into an algebra map `CliffordAlgebra Q →ₐ[ℂ] Matrix …`; `CliffordAlgebra.ι_mul_ι_add_swap` |
| Pauli matrices and their algebra | `!![…]`, `Matrix.conjTranspose`, `norm_matmul`; nothing named Pauli exists |
| Contraction identities in four dimensions (γ_ρ γ^μ γ^ρ = 2γ^μ in the mostly-plus convention, source (47.18)–(47.21)); trace identities if a trace projector is used | `Matrix.trace`, `Matrix.trace_mul_comm`, `Matrix.trace_mul_cycle`, `Matrix.trace_kronecker`; the computation could go either through explicit matrices or through the Clifford relations |
| On-shell spinor algebra (Dirac equation, Gordon identity) and projecting out F₂ | Matrix algebra only; no spinors (1.10, 1.13) |
| Feynman-parameter identity 1/(AB) = ∫₀¹ dx [xA+(1−x)B]⁻², and its n-fold and simplex versions | `intervalIntegral.integral_eq_sub_of_hasDerivAt` (2.11), `integral_rpow`, `Complex.betaIntegral` (3.2); for simplices `stdSimplex`, `MeasureTheory.integral_prod`, `MeasureTheory.volume_preserving_piFinSuccAbove` (2.2). Simplex integration is missing (2.10). |
| Shift of the loop momentum (l = k + x p) | `MeasureTheory.integral_add_right_eq_self` (2.4) |
| Wick rotation of the energy integral (l⁰ = i l⁴_E), or a proof route that avoids it (for example Euclidean-signature definitions plus analytic continuation) | Rectangle Cauchy theorem (5.1) and the vanishing-vertical-sides pattern in `GaussianFourier.tendsto_verticalIntegral` (5.4); `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`; no ray/sector contours, no residue theorem |
| 4D Euclidean integrals ∫ d⁴l (l²+Δ)^(−n) and ∫ d⁴l l² (l²+Δ)^(−n) in closed form | Radial reduction `MeasureTheory.integral_fun_norm_addHaar` (2.6) with `InnerProductSpace.volume_ball_of_dim_even` (2.8). The 1D integral ∫₀^∞ r³(r²+Δ)^(−n) dr reduces to `Complex.betaIntegral` via `MeasureTheory.integral_comp_rpow_Ioi`. The Schwinger route uses `Real.integral_rpow_mul_exp_neg_mul_Ioi` (3.3), Fubini (2.3) and `GaussianFourier.integral_rexp_neg_mul_sq_norm` (3.4). Integrability comes from `integrable_rpow_neg_one_add_norm_sq` (2.9). |
| Symmetric integration / tensor reduction (∫ l^μ l^ν f(l²) = (η^{μν}/4) ∫ l² f(l²); odd integrands vanish) | `LinearIsometryEquiv.measurePreserving`, `MeasureTheory.integral_comp` (2.5), `MeasureTheory.integral_neg_eq_self` (2.4) |
| Closed-form Feynman-parameter integrals in x (rational functions and logs on [0,1]) | `integral_log`, `integral_inv_sq_add_sq`, `integral_id_div_sq_add_sq`, `integral_rpow` (3.5–3.7); FTC (2.11) |
| Regulator limits (UV/IR cutoff or mass parameter → 0⁺) and exchanging limits with integrals | `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` (4.1), `𝓝[>]` (9.2), `TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto` (9.3) |
| Analytic continuation in a mass or momentum parameter (holomorphy of parameter integrals; uniqueness on a cut plane) | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with 𝕜 = ℂ (4.3), `DifferentiableOn.analyticOnNhd` (4.4), identity theorem (5.5), `Complex.cpow`/`Complex.log` on `Complex.slitPlane` (5.6–5.7). Missing: a packaged parameter-holomorphy theorem and connectedness of cut planes. |
| Wick-contraction combinatorics with fermionic signs (if the pilot derives the vertex from a Lagrangian rather than taking Feynman rules as input) | `Equiv.Perm.sign`, `ExteriorAlgebra` (8.1), `Nat.doubleFactorial`, `SimpleGraph.Subgraph.IsPerfectMatching` (8.4). Pfaffians, hafnians and Wick's theorem are missing. |
| Exact order-α bookkeeping (series truncation of amplitudes) | `PowerSeries.trunc`, `PowerSeries.trunc_trunc_mul_trunc`, `PowerSeries.X_pow_dvd_iff` (6.2, 6.4) |

## Focused import set

Each module below was checked to exist as a file at this commit. Redundancy was judged
from the closure of `public import` lines (private and `meta` imports do not re-export),
computed by a script. Lean did not check this, so the sets should be confirmed by the
first focused build. A module is left out when another module in the same set already
provides it through public imports.

| Purpose | Minimal modules (closure-checked) | Already provided by that set (may still be listed explicitly) |
|---|---|---|
| (i) Minkowski metric and gamma matrices over ℂ | `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`, `Mathlib.Basic.Complex.Basic`, `Mathlib.Tactic.NormMatMul` (computation only); optionally `Mathlib.Algebra.Lie.Classical` for `indefiniteDiagonal` | `Mathlib.LinearAlgebra.QuadraticForm.Basic`, `Mathlib.LinearAlgebra.Matrix.Trace`, `Mathlib.LinearAlgebra.Matrix.ConjTranspose`, `Mathlib.LinearAlgebra.Matrix.Kronecker`, `Mathlib.Data.Matrix.Block`, `Mathlib.LinearAlgebra.Matrix.Notation` (all provided by `CliffordAlgebra.Basic`). Use `Mathlib.Basic.Complex.Basic`, not the deprecated `Mathlib.Data.Complex.Basic`. |
| (ii) 4D radial / Euclidean loop integrals | `Mathlib.MeasureTheory.Constructions.HaarToSphere`, `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls`, `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`; optionally `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform` for the Gaussian/Schwinger route | `Mathlib.MeasureTheory.Integral.Prod` and `Mathlib.MeasureTheory.Constructions.Pi` (via `HaarToSphere`); `Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace`, `Mathlib.Analysis.SpecialFunctions.JapaneseBracket`, `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`, `Mathlib.MeasureTheory.Group.Integral`, `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, `Mathlib.MeasureTheory.Integral.IntegralEqImproper`, `Mathlib.MeasureTheory.Function.Jacobian` (via `VolumeOfBalls`) |
| (iii) Parametric holomorphy and the identity theorem | `Mathlib.Analysis.SpecialFunctions.Complex.Analytic`, `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`, `Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv`, `Mathlib.Analysis.Complex.Convex` | `Mathlib.Analysis.Complex.CauchyIntegral` (via `Complex.Analytic`), and through it `Mathlib.Analysis.Calculus.ParametricIntegral`, `Mathlib.Analysis.Calculus.ParametricIntervalIntegral`, `Mathlib.Analysis.Analytic.Uniqueness`, `Mathlib.Analysis.Analytic.IsolatedZeros`, `Mathlib.MeasureTheory.Integral.DominatedConvergence`, `Mathlib.Analysis.Convex.PathConnected` |

For a first module, Mathlib style favors importing the modules that are actually used
(for example `Mathlib.LinearAlgebra.Matrix.Trace` or
`Mathlib.Analysis.Calculus.ParametricIntegral`) over relying on transitive closure.
Adding them does not enlarge the build, because they are already in the closure.
