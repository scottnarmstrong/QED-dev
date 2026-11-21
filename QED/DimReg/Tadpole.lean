/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Basic
public import QED.DimReg.BetaPrime
public import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The one-loop massive tadpole in `d` dimensions

The one-loop tadpole `∫ dᵈk / π ^ (d / 2) · 1 / (k² + m²) ^ ν` has one Feynman parameter, with
Symanzik polynomials `U = x` and `F = m² x²` (`QED.DimReg.tadpoleFamily`). Its Lee–Pomeransky
integral `∫₀^∞ x ^ (ν - 1) (x + m² x²) ^ (-d / 2) dx` converges absolutely on the strip
`re (d / 2) < re ν < re d`, where it equals
`(m²) ^ (d / 2 - ν) Γ(ν - d / 2) Γ(d - ν) / Γ(d / 2)`. With the Γ-prefactor
`Γ(d / 2) / (Γ(d - ν) Γ(ν))` this gives the textbook closed form
`I(d, ν) = Γ(ν - d / 2) / Γ(ν) · (m²) ^ (d / 2 - ν)`.

The closed form `QED.DimReg.tadpole` is meromorphic in `d` on all of `ℂ`, so it is the
meromorphic continuation of the integral off the strip of convergence.

## Main results

* `QED.DimReg.lpConvergent_tadpole`: absolute convergence on the strip.
* `QED.DimReg.lpIntegral_tadpole`: the closed form of the Lee–Pomeransky integral.
* `QED.DimReg.integral_tadpoleFamily`: `I(d, ν) = Γ(ν - d / 2) / Γ(ν) · (m²) ^ (d / 2 - ν)`.
* `QED.DimReg.meromorphic_tadpole`, `QED.DimReg.meromorphic_tadpoleLP`: the closed forms are
  meromorphic in `d` on `ℂ`.
* `QED.DimReg.tadpole_meromorphicContinuation`: the normalized integral agrees on the strip of
  convergence with a function meromorphic on `ℂ`.
-/

@[expose] public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg

/-- The one-loop massive tadpole family: one propagator, `L = 1`, `U = x`, `F = m² x²`. -/
noncomputable def tadpoleFamily (m2 : ℝ) : FeynmanFamily 1 where
  loops := 1
  U := X 0
  F := C m2 * X 0 ^ 2

theorem tadpoleFamily_isHomogeneous (m2 : ℝ) : (tadpoleFamily m2).IsHomogeneous := by
  refine ⟨isHomogeneous_X _ _, ?_⟩
  exact (isHomogeneous_C _ _).mul ((isHomogeneous_X _ _).pow 2)

theorem lpPoly_tadpoleFamily (m2 : ℝ) (x : Fin 1 → ℝ) :
    (tadpoleFamily m2).lpPoly x = x 0 + m2 * x 0 ^ 2 := by
  simp [FeynmanFamily.lpPoly, tadpoleFamily]

/-- The one-variable tadpole integrand `y ↦ y ^ (ν - 1) (y + m² y²) ^ (-d / 2)`. -/
noncomputable def tadpoleIntegrand (m2 : ℝ) (ν d : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (ν - 1) * ((y + m2 * y ^ 2 : ℝ) : ℂ) ^ (-(d / 2))

theorem lpIntegrand_tadpoleFamily (m2 : ℝ) (ν d : ℂ) (x : Fin 1 → ℝ) :
    lpIntegrand (tadpoleFamily m2).lpPoly (fun _ => ν) d x =
      tadpoleIntegrand m2 ν d (MeasurableEquiv.funUnique (Fin 1) ℝ x) := by
  simp [lpIntegrand, tadpoleIntegrand, lpPoly_tadpoleFamily]

theorem preimage_funUnique_Ioi :
    (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioi 0 = posOrthant 1 := by
  ext x
  simp [mem_posOrthant, Fin.forall_fin_one]

/-- On `(0, ∞)` the tadpole integrand is the Beta integrand of the second kind with
`a = ν - d / 2`, `b = d - ν`, `c = m²`. -/
theorem tadpoleIntegrand_eq {m2 : ℝ} (hm : 0 < m2) (ν d : ℂ) {y : ℝ} (hy : 0 < y) :
    tadpoleIntegrand m2 ν d y = betaPrimeIntegrand (ν - d / 2) (d - ν) m2 y := by
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [tadpoleIntegrand, betaPrimeIntegrand, show y + m2 * y ^ 2 = y * (1 + m2 * y) by ring,
    ofReal_mul, mul_cpow_ofReal_nonneg hy.le (by positivity), ← mul_assoc, ← cpow_add _ _ hy0]
  congr 2 <;> ring

theorem integrableOn_tadpoleIntegrand {m2 : ℝ} (hm : 0 < m2) {ν d : ℂ}
    (h1 : 0 < (ν - d / 2).re) (h2 : 0 < (d - ν).re) :
    IntegrableOn (tadpoleIntegrand m2 ν d) (Ioi 0) :=
  (integrableOn_betaPrime h1 h2 hm).congr_fun
    (fun _ hy => (tadpoleIntegrand_eq hm ν d hy).symm) measurableSet_Ioi

/-- The tadpole's Lee–Pomeransky integral converges absolutely on the strip
`re (d / 2) < re ν < re d`. -/
theorem lpConvergent_tadpole {m2 : ℝ} (hm : 0 < m2) {ν d : ℂ}
    (h1 : 0 < (ν - d / 2).re) (h2 : 0 < (d - ν).re) :
    LPConvergent (tadpoleFamily m2).lpPoly (fun _ => ν) d := by
  have e := (volume_preserving_funUnique (Fin 1) ℝ).integrableOn_comp_preimage
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
    (f := tadpoleIntegrand m2 ν d) (s := Ioi 0)
  rw [preimage_funUnique_Ioi] at e
  unfold LPConvergent
  refine (e.mpr (integrableOn_tadpoleIntegrand hm h1 h2)).congr_fun
    (fun x _ => (lpIntegrand_tadpoleFamily m2 ν d x).symm) (measurableSet_posOrthant 1)

/-- The closed form of the tadpole's Lee–Pomeransky integral on the strip of convergence:
`∫₀^∞ x ^ (ν - 1) (x + m² x²) ^ (-d / 2) dx = (m²) ^ (d / 2 - ν) Γ(ν - d / 2) Γ(d - ν) / Γ(d / 2)`.
-/
theorem lpIntegral_tadpole {m2 : ℝ} (hm : 0 < m2) {ν d : ℂ}
    (h1 : 0 < (ν - d / 2).re) (h2 : 0 < (d - ν).re) :
    lpIntegral (tadpoleFamily m2).lpPoly (fun _ => ν) d =
      (m2 : ℂ) ^ (d / 2 - ν) * (Gamma (ν - d / 2) * Gamma (d - ν) / Gamma (d / 2)) := by
  have e := (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding (tadpoleIntegrand m2 ν d) (Ioi 0)
  rw [preimage_funUnique_Ioi] at e
  have e0 : lpIntegral (tadpoleFamily m2).lpPoly (fun _ => ν) d =
      ∫ x in posOrthant 1, tadpoleIntegrand m2 ν d (MeasurableEquiv.funUnique (Fin 1) ℝ x) := by
    rw [lpIntegral]
    simp_rw [lpIntegrand_tadpoleFamily]
  rw [e0.trans e,
    setIntegral_congr_fun measurableSet_Ioi (fun _ hy => tadpoleIntegrand_eq hm ν d hy),
    integral_betaPrime h1 h2 hm]
  congr 2
  · ring
  · ring_nf

/-- The closed form of the normalized one-loop tadpole,
`Γ(ν - d / 2) / Γ(ν) · (m²) ^ (d / 2 - ν)`. For fixed `ν` and `m² > 0` it is meromorphic in
`d` on `ℂ` (`QED.DimReg.meromorphic_tadpole`). -/
noncomputable def tadpole (m2 : ℝ) (ν d : ℂ) : ℂ :=
  Gamma (ν - d / 2) / Gamma ν * (m2 : ℂ) ^ (d / 2 - ν)

/-- The closed form of the tadpole's Lee–Pomeransky integral,
`(m²) ^ (d / 2 - ν) Γ(ν - d / 2) Γ(d - ν) / Γ(d / 2)`. -/
noncomputable def tadpoleLP (m2 : ℝ) (ν d : ℂ) : ℂ :=
  (m2 : ℂ) ^ (d / 2 - ν) * (Gamma (ν - d / 2) * Gamma (d - ν) / Gamma (d / 2))

/-- The normalized tadpole integral equals its closed form on the strip of convergence:
`I(d, ν) = Γ(ν - d / 2) / Γ(ν) · (m²) ^ (d / 2 - ν)`. -/
theorem integral_tadpoleFamily {m2 : ℝ} (hm : 0 < m2) {ν d : ℂ}
    (h1 : 0 < (ν - d / 2).re) (h2 : 0 < (d - ν).re) :
    (tadpoleFamily m2).integral (fun _ => ν) d = tadpole m2 ν d := by
  have hd : 0 < (d / 2).re := by
    have : d / 2 = (ν - d / 2) + (d - ν) := by ring
    rw [this, add_re]; linarith
  have hν : 0 < ν.re := by
    have : ν = (ν - d / 2) + (d / 2) := by ring
    rw [this, add_re]; linarith
  have g1 := Gamma_ne_zero_of_re_pos hd
  have g2 := Gamma_ne_zero_of_re_pos h2
  have g3 := Gamma_ne_zero_of_re_pos hν
  rw [FeynmanFamily.integral, lpIntegral_tadpole hm h1 h2, FeynmanFamily.prefactor, tadpole]
  simp only [tadpoleFamily, Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton]
  rw [show ((1 : ℕ) + 1 : ℂ) * d / 2 - ν = d - ν by push_cast; ring]
  field_simp

theorem analyticAt_ofReal_cpow {c : ℝ} (hc : 0 < c) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (z : ℂ) : AnalyticAt ℂ (fun d => (c : ℂ) ^ f d) z := by
  refine Differentiable.analyticAt (fun w => ?_) z
  exact (hf w).const_cpow (Or.inl (ofReal_ne_zero.mpr hc.ne'))

theorem meromorphicAt_Gamma_comp {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    MeromorphicAt (fun d => Gamma (f d)) z :=
  (Meromorphic.Gamma (f z)).comp_analyticAt hf

/-- The tadpole closed form is meromorphic in `d` on all of `ℂ`. -/
theorem meromorphic_tadpole {m2 : ℝ} (hm : 0 < m2) (ν : ℂ) :
    Meromorphic fun d => tadpole m2 ν d := by
  intro z
  unfold tadpole
  refine ((meromorphicAt_Gamma_comp (by fun_prop)).div (MeromorphicAt.const _ _)).mul
    (analyticAt_ofReal_cpow hm _ (by fun_prop) z).meromorphicAt

/-- The closed form of the tadpole's Lee–Pomeransky integral is meromorphic in `d` on `ℂ`. -/
theorem meromorphic_tadpoleLP {m2 : ℝ} (hm : 0 < m2) (ν : ℂ) :
    Meromorphic fun d => tadpoleLP m2 ν d := by
  intro z
  unfold tadpoleLP
  refine (analyticAt_ofReal_cpow hm _ (by fun_prop) z).meromorphicAt.mul
    (((meromorphicAt_Gamma_comp (by fun_prop)).mul
      (meromorphicAt_Gamma_comp (by fun_prop))).div (meromorphicAt_Gamma_comp (by fun_prop)))

/-- Meromorphic continuation of the normalized tadpole: the integral `I(d, ν)` agrees on its
strip of absolute convergence with the function `tadpole m2 ν`, which is meromorphic on `ℂ`. -/
theorem tadpole_meromorphicContinuation {m2 : ℝ} (hm : 0 < m2) (ν : ℂ) :
    Meromorphic (fun d => tadpole m2 ν d) ∧
      ∀ d : ℂ, 0 < (ν - d / 2).re → 0 < (d - ν).re →
        LPConvergent (tadpoleFamily m2).lpPoly (fun _ => ν) d ∧
          (tadpoleFamily m2).integral (fun _ => ν) d = tadpole m2 ν d :=
  ⟨meromorphic_tadpole hm ν, fun _ h1 h2 =>
    ⟨lpConvergent_tadpole hm h1 h2, integral_tadpoleFamily hm h1 h2⟩⟩

end QED.DimReg
