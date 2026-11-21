/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Dimensionally continued Feynman-parametric integrals (Lee–Pomeransky form)

This file sets up layer L1 of the analytic three-loop route: Euclidean Feynman integrals as
functions of a complex dimension `d`, in Feynman-parametric form.

## The formulation

Let a scalar Feynman integral have `N` propagators with exponents `ν : Fin N → ℂ`, `L` loops, and
first and second Symanzik polynomials `U` (homogeneous of degree `L`) and `F` (homogeneous of
degree `L + 1`). With the Euclidean loop measure `∏ₗ dᵈkₗ / π ^ (d / 2)`, the Lee–Pomeransky
representation reads
`I(d, ν) = Γ(d / 2) / (Γ((L + 1) d / 2 - |ν|) ∏ᵢ Γ(νᵢ)) · ∫_{(0,∞)^N} ∏ᵢ xᵢ ^ (νᵢ - 1) ·
  G(x) ^ (-d / 2) dx`, with `G = U + F` and `|ν| = ∑ᵢ νᵢ`.
We define the integral by this formula (`FeynmanFamily.integral`), with the parametric integral
`lpIntegral` as the basic object.

We choose the Lee–Pomeransky form over the projective (simplex) form
`∫ δ(1 - ∑ x) x ^ (ν - 1) U ^ (|ν| - (L + 1) d / 2) F ^ (-|ν| + L d / 2)` for the following
reasons.
* **No delta function.** The domain is the open orthant `(0, ∞)^N` with Lebesgue measure, a
  product set. Fubini, the one-variable integration by parts `∫₀^∞ x ^ (a - 1) f = -(1 / a) ∫₀^∞
  x ^ a f'` that drives the meromorphic continuation, and changes of variables in one coordinate
  apply directly; on the simplex every such step needs a choice of chart.
* **One polynomial, one exponent.** The integrand is `x ^ (ν - 1) G ^ (-d / 2)` with a single
  polynomial `G`, and `d` enters only through one exponent. Integration-by-parts identities
  are the vanishing of `∫ ∂ᵢ (xᵢ · x ^ (ν - 1) G ^ (-d / 2))`; multiplication by `xᵢ` is the
  shift `νᵢ ↦ νᵢ + 1`, and `∂ᵢ G ^ (-d / 2) = -(d / 2) (∂ᵢ G) G ^ (-d / 2 - 1)` is the shift
  `d ↦ d + 2`. Every such identity is a polynomial identity in `x`, `ν` and `d` (the annihilator
  form of Bitoun–Bogner–Klausen–Panzer), which is the shape a kernel-checked certificate needs.
* **Real positive integrand.** For Euclidean (or on-shell, below-threshold) kinematics `G > 0`
  on the orthant, so `G ^ (-d / 2)` is the principal power of a positive real; its norm is
  `G ^ (-re d / 2)`, and absolute convergence depends only on `re d` and `re ν`
  (`QED.DimReg.lpConvergent_iff_re`).
* **The Γ-prefactor is separate.** All poles in `d` that come from the overall scaling sit in
  the explicit prefactor, which is meromorphic because `Γ` is (`Meromorphic.Gamma`).

Non-integer `d` is an evaluation device only; nothing here changes the physical model.

## Main definitions

* `QED.DimReg.posOrthant N`: the open orthant `(0, ∞)^N`.
* `QED.DimReg.lpIntegrand G ν d x = ∏ᵢ xᵢ ^ (νᵢ - 1) · G(x) ^ (-d / 2)`.
* `QED.DimReg.lpIntegral G ν d`: its integral over the orthant.
* `QED.DimReg.LPConvergent G ν d`: absolute convergence (integrability on the orthant);
  `QED.DimReg.lpConvergenceRegion G ν` is the set of such `d`.
* `QED.DimReg.FeynmanFamily N`: loop number and Symanzik polynomials `U`, `F` of a family.
* `QED.DimReg.FeynmanFamily.integral`: the normalized Feynman integral `I(d, ν)`.

## Main results

* `QED.DimReg.norm_lpIntegrand`: the norm of the integrand where `G > 0`.
* `QED.DimReg.lpConvergent_iff_re`: convergence depends only on `re ν` and `re d`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.DimReg

variable {N : ℕ}

/-- The open positive orthant `(0, ∞)^N`, the domain of the Lee–Pomeransky integral. -/
def posOrthant (N : ℕ) : Set (Fin N → ℝ) := univ.pi fun _ => Ioi 0

theorem measurableSet_posOrthant (N : ℕ) : MeasurableSet (posOrthant N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

theorem mem_posOrthant {x : Fin N → ℝ} : x ∈ posOrthant N ↔ ∀ i, 0 < x i := by
  simp [posOrthant]

/-- The Lee–Pomeransky integrand `∏ᵢ xᵢ ^ (νᵢ - 1) · G(x) ^ (-d / 2)`, with complex
exponents and principal powers. -/
noncomputable def lpIntegrand (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (d : ℂ)
    (x : Fin N → ℝ) : ℂ :=
  (∏ i, (x i : ℂ) ^ (ν i - 1)) * (G x : ℂ) ^ (-(d / 2))

/-- The Lee–Pomeransky parametric integral `∫_{(0,∞)^N} ∏ᵢ xᵢ ^ (νᵢ - 1) G(x) ^ (-d / 2) dx`.
It is the Bochner integral, so it is meaningful (and equal to the absolutely convergent
integral) exactly where `LPConvergent G ν d` holds; elsewhere it is `0`, and the value in `d`
is given by a meromorphic continuation. -/
noncomputable def lpIntegral (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (d : ℂ) : ℂ :=
  ∫ x in posOrthant N, lpIntegrand G ν d x

/-- Absolute convergence of the Lee–Pomeransky integral. -/
def LPConvergent (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (d : ℂ) : Prop :=
  IntegrableOn (lpIntegrand G ν d) (posOrthant N)

/-- The region of absolute convergence in the dimension `d`. -/
def lpConvergenceRegion (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) : Set ℂ :=
  {d | LPConvergent G ν d}

/-- The data of a scalar Feynman integral family in parametric form: the loop number and the
first and second Symanzik polynomials `U` and `F` in the `N` Feynman parameters. -/
structure FeynmanFamily (N : ℕ) where
  /-- The loop number `L`. -/
  loops : ℕ
  /-- The first Symanzik polynomial `U`, homogeneous of degree `L`. -/
  U : MvPolynomial (Fin N) ℝ
  /-- The second Symanzik polynomial `F` (masses included), homogeneous of degree `L + 1`. -/
  F : MvPolynomial (Fin N) ℝ

namespace FeynmanFamily

/-- The homogeneity conditions on the Symanzik polynomials. -/
def IsHomogeneous (P : FeynmanFamily N) : Prop :=
  MvPolynomial.IsHomogeneous P.U P.loops ∧ MvPolynomial.IsHomogeneous P.F (P.loops + 1)

/-- The Lee–Pomeransky polynomial `G = U + F`, as a function on `ℝ^N`. -/
noncomputable def lpPoly (P : FeynmanFamily N) (x : Fin N → ℝ) : ℝ :=
  MvPolynomial.eval x (P.U + P.F)

/-- The Γ-prefactor `Γ(d / 2) / (Γ((L + 1) d / 2 - |ν|) ∏ᵢ Γ(νᵢ))` of the Lee–Pomeransky
representation. -/
noncomputable def prefactor (P : FeynmanFamily N) (ν : Fin N → ℂ) (d : ℂ) : ℂ :=
  Gamma (d / 2) / (Gamma ((P.loops + 1) * d / 2 - ∑ i, ν i) * ∏ i, Gamma (ν i))

/-- The dimensionally continued Euclidean Feynman integral of the family, normalized by the
loop measure `∏ₗ dᵈkₗ / π ^ (d / 2)`:
`I(d, ν) = Γ(d / 2) / (Γ((L + 1) d / 2 - |ν|) ∏ᵢ Γ(νᵢ)) · ∫ x ^ (ν - 1) G ^ (-d / 2)`.
It is meaningful where `LPConvergent P.lpPoly ν d` holds; outside, the meromorphic
continuation of this expression is the value. -/
noncomputable def integral (P : FeynmanFamily N) (ν : Fin N → ℂ) (d : ℂ) : ℂ :=
  P.prefactor ν d * lpIntegral P.lpPoly ν d

theorem continuous_lpPoly (P : FeynmanFamily N) : Continuous P.lpPoly :=
  MvPolynomial.continuous_eval _

end FeynmanFamily

/-- On the orthant, where `G > 0`, the norm of the integrand is the real integrand
`∏ᵢ xᵢ ^ (re νᵢ - 1) · G(x) ^ (-re d / 2)`. -/
theorem norm_lpIntegrand (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (d : ℂ) {x : Fin N → ℝ}
    (hx : x ∈ posOrthant N) (hG : 0 < G x) :
    ‖lpIntegrand G ν d x‖ = (∏ i, x i ^ ((ν i).re - 1)) * G x ^ (-(d.re / 2)) := by
  rw [mem_posOrthant] at hx
  simp only [lpIntegrand, norm_mul, norm_prod, norm_cpow_eq_rpow_re_of_pos (hx _),
    norm_cpow_eq_rpow_re_of_pos hG, sub_re, one_re, neg_re, div_re]
  norm_num
  left
  congr 1
  ring

theorem measurable_lpIntegrand {G : (Fin N → ℝ) → ℝ} (hG : Measurable G) (ν : Fin N → ℂ)
    (d : ℂ) : Measurable (lpIntegrand G ν d) := by
  unfold lpIntegrand
  refine Measurable.mul ?_ ?_
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_ofReal.comp (measurable_pi_apply i)).pow_const _
  · exact (measurable_ofReal.comp hG).pow_const _

/-- The absolute convergence of the Lee–Pomeransky integral depends only on `re ν` and `re d`:
it is the integrability of the positive real integrand. -/
theorem lpConvergent_iff_re {G : (Fin N → ℝ) → ℝ} (hG : Measurable G)
    (hpos : ∀ x ∈ posOrthant N, 0 < G x) (ν : Fin N → ℂ) (d : ℂ) :
    LPConvergent G ν d ↔ IntegrableOn
      (fun x => (∏ i, x i ^ ((ν i).re - 1)) * G x ^ (-(d.re / 2))) (posOrthant N) := by
  unfold LPConvergent IntegrableOn
  rw [← integrable_norm_iff (measurable_lpIntegrand hG ν d).aestronglyMeasurable]
  exact integrableOn_congr_fun (fun x hx => norm_lpIntegrand G ν d hx (hpos x hx))
    (measurableSet_posOrthant N)

/-- Corollary: convergence at `(ν, d)` is the same as at `(re ν, re d)`. -/
theorem lpConvergent_iff_lpConvergent_re {G : (Fin N → ℝ) → ℝ} (hG : Measurable G)
    (hpos : ∀ x ∈ posOrthant N, 0 < G x) (ν : Fin N → ℂ) (d : ℂ) :
    LPConvergent G ν d ↔ LPConvergent G (fun i => ((ν i).re : ℂ)) (d.re : ℂ) := by
  rw [lpConvergent_iff_re hG hpos, lpConvergent_iff_re hG hpos]
  simp

end QED.DimReg
