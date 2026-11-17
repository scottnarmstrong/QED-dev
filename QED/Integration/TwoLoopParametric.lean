/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopParametricAlgebra
public import QED.Integration.TwoLoopEnergyIntegral
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The scalar two-loop parametric representation

The assembly of obligation O2-10 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.3–4.4) for scalar
propagators. For `N = m + 1 ≥ 5` propagators with line momenta `kᵢ(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ`, masses
`Mᵢ` and `ε > 0`, the denominators `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε` (mostly-plus metric, the convention of
the frozen one-loop propagators) satisfy
`jointEnergyFirstIntegral 2 (∏ᵢ Dᵢ⁻¹) = -π⁴ (N-5)! ∫_{Δ} U(z)⁻² (V(z) - iε)^{4-N} dx`,
with `z = (x, 1 - ∑ xᵢ)`, `U = det A(z)`, `A(z)ₛₜ = ∑ᵢ zᵢ αᵢₛ αᵢₜ` and `V` the remainder
`QED.Integration.TwoLoop.symanzikV`, both stages of the joint integral being integrable.

## Hypotheses

* `N ≥ 5` (`4 ≤ m`): the six-dimensional spatial integral `∫ (vᵀAv + w)^{-(N-1)}` needs
  `N - 1 ≥ 4`; for `N ≤ 4` the overall integral diverges logarithmically or worse.
* Two of the `αᵢ` are linearly independent: then `A(z)` is positive definite on the interior of the
  simplex, whose boundary is null (`ae_simplexPoint_ne_zero`).
* `U⁻²` is integrable on the simplex. This is exactly the absolute convergence of the
  parametrized integral over simplex × space (the energy-integrated, parametrized integrand has
  absolute spatial integral `≍ U^{-1/2} U^{-3/2}`); it fails precisely when a one-loop
  subintegration diverges (`U → 0` at the faces where the `zᵢ` concentrate on lines with parallel
  `αᵢ`, CK-UV (2.3)). It implies the integrability of `U^{-1/2}` used for the energy swap.

## Order of integration

The joint prescription integrates the energies `t` first at fixed spatial momenta `v`. The
Feynman formula is applied pointwise at fixed `(t, v)`. At fixed `v` the swap simplex × energies
is absolutely justified: `∫ |∑ zᵢDᵢ|^{-N} dt ≤ C(v, ε) U^{-1/2}` uniformly on the simplex, because
the real part of the shifted constant is bounded there (`abs_re_shifted_le`). The signed energy
integral gives `-(π/(N-1)) U^{-1/2} w^{1-N}`, `w = (v+σ)ᵀA(v+σ) + V - iε`. The swap
simplex × space is then absolutely justified by `∫ |w|^{1-N} dv ≤ C(ε) U^{-3/2}` (`|V|` is bounded
on the simplex, `abs_symanzikV_le`) and the integrability of `U⁻²`. Tonelli on energies × space
is never used (section 4.3 shows it fails after parametrization).

## Main statements

* `integral_prod_lineDenom_eq` (sub-step (a)): at fixed `v`, the energy integral of `∏ᵢ Dᵢ⁻¹`
  is `(N-1)!` times the simplex integral of the two-dimensional formula, with integrability; it
  needs only `U^{-1/2}` integrable (implied by `U⁻²` integrable, `integrableOn_inv_sqrt_symanzikU`).
* `jointEnergyFirstIntegral_prod_inv_lineDenom`: the full parametric representation, with the
  integrability of both stages.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter Function
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint simplexComb)
open QED.Integration.Spatial (quadForm)

variable {m : ℕ}

/-! ### Fixed positive definite `A`: the energy integral -/

theorem dotProduct_mulVec_self_nonneg {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (y : Fin 2 → ℝ) : 0 ≤ y ⬝ᵥ A *ᵥ y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have := hA.dotProduct_mulVec_pos hy
    rw [star_trivial] at this
    exact this.le

theorem quadForm_nonneg {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (v : Fin 2 → Fin 3 → ℝ) : 0 ≤ quadForm A v := by
  rw [quadForm_eq_sum_dotProduct]
  exact Finset.sum_nonneg fun c _ => dotProduct_mulVec_self_nonneg hA _

theorem integrable_inv_neg_shifted_quadratic_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) (τ : Fin 2 → ℝ) :
    Integrable fun t : Fin 2 → ℝ => ((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ n)⁻¹ :=
  (integrable_inv_neg_quadratic_add_pow hA hw hn).comp_add_right τ

theorem integral_inv_neg_shifted_quadratic_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) (τ : Fin 2 → ℝ) :
    ∫ t : Fin 2 → ℝ, ((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ n)⁻¹ =
      -(π / ((n : ℂ) - 1)) * ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 1))⁻¹ := by
  rw [integral_add_right_eq_self (fun t : Fin 2 → ℝ => ((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + w) ^ n)⁻¹) τ]
  exact integral_inv_neg_quadratic_add_pow hA hw hn

/-- Linear change of variables for real integrands. -/
theorem integral_comp_mulVec_real {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Matrix ι ι ℝ}
    (hN : N.det ≠ 0) (g : (ι → ℝ) → ℝ) :
    ∫ u, g (N *ᵥ u) = |N.det|⁻¹ * ∫ u, g u := by
  have h := Spatial.integral_comp_mulVec hN (fun u => (g u : ℂ))
  simp only [real_smul] at h
  exact_mod_cast h

/-- The constant `∫_{ℝ²} ‖(-|s|² - i)^{-n}‖ ds`. -/
noncomputable def energyNormConst (n : ℕ) : ℝ :=
  ∫ s : Fin 2 → ℝ, ‖((-((s 0 ^ 2 + s 1 ^ 2 : ℝ) : ℂ) + -I) ^ n)⁻¹‖

theorem integral_norm_inv_neg_quadratic {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (n : ℕ) :
    ∫ t : Fin 2 → ℝ, ‖((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + -I) ^ n)⁻¹‖ =
      (Real.sqrt A.det)⁻¹ * energyNormConst n := by
  have hpos : 0 < Real.sqrt A.det := Real.sqrt_pos.mpr hA.det_pos
  have hM : (cholesky A).det ≠ 0 := by rw [det_cholesky hA]; exact hpos.ne'
  set g : (Fin 2 → ℝ) → ℝ := fun s => ‖((-((s 0 ^ 2 + s 1 ^ 2 : ℝ) : ℂ) + -I) ^ n)⁻¹‖
  have hfun : (fun t : Fin 2 → ℝ => ‖((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + -I) ^ n)⁻¹‖) =
      fun t => g (cholesky A *ᵥ t) := by
    funext t
    simp only [g, dotProduct_mulVec_eq_cholesky hA t]
  rw [hfun, integral_comp_mulVec_real hM g, det_cholesky hA, abs_of_pos hpos]
  rfl

/-- The uniform energy bound `∫ ‖(-(t+τ)ᵀA(t+τ) + w)^{-n}‖ dt ≤ (√δ)^{-n} (det A)^{-1/2} K₁`. -/
theorem integral_norm_inv_neg_shifted_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {w : ℂ} {K ε δ : ℝ} (hw : |w.re| ≤ K) (hwi : w.im = -ε) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {n : ℕ} (hn : 2 ≤ n) (τ : Fin 2 → ℝ) :
    ∫ t : Fin 2 → ℝ, ‖((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ n)⁻¹‖ ≤
      (Real.sqrt δ ^ n)⁻¹ * ((Real.sqrt A.det)⁻¹ * energyNormConst n) := by
  rw [integral_add_right_eq_self (fun t : Fin 2 → ℝ => ‖((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + w) ^ n)⁻¹‖) τ,
    ← integral_norm_inv_neg_quadratic hA n, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) ?_
    (Eventually.of_forall fun t => ?_)
  · exact (integrable_inv_neg_quadratic_add_pow hA (w := -I) (by simp) hn).norm.const_mul _
  · exact norm_inv_neg_add_pow_le_uniform (dotProduct_mulVec_self_nonneg hA t) hw hwi hδ0 hδ hδε n

/-! ### Fixed positive definite `A`: the spatial integral -/

theorem integrable_inv_quadForm_shifted_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {w : ℂ} (hw : w.im < 0) {k : ℕ} (hk : 4 ≤ k) (σ : Fin 2 → Fin 3 → ℝ) :
    Integrable fun v : Fin 2 → Fin 3 → ℝ => ((((quadForm A (v + σ) : ℝ) : ℂ) + w) ^ k)⁻¹ :=
  (Spatial.integrable_inv_quadForm_add_pow hA (mem_slitPlane_iff.mpr (Or.inr hw.ne)) hk).comp_add_right σ

theorem integral_inv_quadForm_shifted_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {w : ℂ} (hw : w.im < 0) {k : ℕ} (hk : 4 ≤ k) (σ : Fin 2 → Fin 3 → ℝ) :
    ∫ v : Fin 2 → Fin 3 → ℝ, ((((quadForm A (v + σ) : ℝ) : ℂ) + w) ^ k)⁻¹ =
      (π : ℂ) ^ 3 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3))⁻¹ *
        ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 3))⁻¹ := by
  rw [integral_add_right_eq_self
    (fun v : Fin 2 → Fin 3 → ℝ => ((((quadForm A v : ℝ) : ℂ) + w) ^ k)⁻¹) σ]
  exact Spatial.integral_inv_quadForm_add_pow_of_im_neg hA hw hk

theorem integral_norm_inv_quadForm_add_one {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {k : ℕ} (hk : 4 ≤ k) :
    ∫ v : Fin 2 → Fin 3 → ℝ, ‖((((quadForm A v : ℝ) : ℂ) + 1) ^ k)⁻¹‖ =
      π ^ 3 * (((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3))⁻¹ * (Real.sqrt A.det ^ 3)⁻¹ := by
  have hnorm : ∀ v : Fin 2 → Fin 3 → ℝ, ‖((((quadForm A v : ℝ) : ℂ) + 1) ^ k)⁻¹‖ =
      ((quadForm A v + 1) ^ k)⁻¹ := by
    intro v
    have h0 := quadForm_nonneg hA v
    rw [show ((quadForm A v : ℝ) : ℂ) + 1 = ((quadForm A v + 1 : ℝ) : ℂ) by push_cast; ring,
      norm_inv, norm_pow, norm_real, Real.norm_of_nonneg (by linarith)]
  simp only [hnorm]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  rw [Spatial.integral_inv_quadForm_add_pow hA (w := 1) one_mem_slitPlane hk, one_pow, inv_one,
    mul_one]
  push_cast
  ring

/-- The uniform spatial bound
`∫ ‖((v+σ)ᵀA(v+σ) + V - iε)^{-k}‖ dv ≤ (√δ)^{-k} π³/((k-1)(k-2)(k-3)) (det A)^{-3/2}`. -/
theorem integral_norm_inv_quadForm_shifted_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {V K ε δ : ℝ} (hV : |V| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {k : ℕ} (hk : 4 ≤ k) (σ : Fin 2 → Fin 3 → ℝ) :
    ∫ v : Fin 2 → Fin 3 → ℝ, ‖((((quadForm A (v + σ) : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ k)⁻¹‖ ≤
      (Real.sqrt δ ^ k)⁻¹ *
        (π ^ 3 * (((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3))⁻¹ * (Real.sqrt A.det ^ 3)⁻¹) := by
  rw [integral_add_right_eq_self (fun v : Fin 2 → Fin 3 → ℝ =>
      ‖((((quadForm A v : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ k)⁻¹‖) σ,
    ← integral_norm_inv_quadForm_add_one hA hk, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _) ?_
    (Eventually.of_forall fun v => ?_)
  · exact (Spatial.integrable_inv_quadForm_add_pow hA (w := 1) one_mem_slitPlane hk).norm.const_mul _
  · exact norm_inv_add_pow_le_uniform (quadForm_nonneg hA v) hV hδ0 hδ hδε k

/-! ### The parametrized functions -/

/-- The combined Feynman denominator `∑ᵢ zᵢ Dᵢ(t, v)` at `z = simplexPoint x`. -/
noncomputable def paramDenom (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (x : Fin m → ℝ) (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) : ℂ :=
  simplexComb (fun i => lineDenom α p M ε i (loopMomenta t v)) x

/-- The constant after the energy shift: `w = (v+σ)ᵀA(v+σ) + V - iε` at `z = simplexPoint x`. -/
noncomputable def shiftedConst (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) : ℂ :=
  ((quadForm (symanzikMatrix α (simplexPoint x)) (v + spatialShift α p (simplexPoint x)) : ℝ) : ℂ) +
    (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)

/-- The energy-integrated parametrized integrand `-(π/(N-1)) U^{-1/2} w^{1-N}`, `N = m + 1`. -/
noncomputable def energyValue (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) : ℂ :=
  -(π / (((m + 1 : ℕ) : ℂ) - 1)) * ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
    (shiftedConst α p M ε x v ^ (m + 1 - 1))⁻¹

variable (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
  {ε : ℝ}

theorem paramDenom_im (x : Fin m → ℝ) (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    (paramDenom α p M ε x t v).im = -ε := by
  rw [paramDenom, Feynman.simplexComb_im]
  simp only [lineDenom, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, zero_sub,
    mul_one, mul_neg]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

theorem paramDenom_eq {x : Fin m → ℝ} (hdet : symanzikU α (simplexPoint x) ≠ 0)
    (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    paramDenom α p M ε x t v =
      -(((t + energyShift α p (simplexPoint x)) ⬝ᵥ symanzikMatrix α (simplexPoint x) *ᵥ
        (t + energyShift α p (simplexPoint x)) : ℝ) : ℂ) + shiftedConst α p M ε x v := by
  rw [paramDenom, Feynman.simplexComb_eq_sum_simplexPoint,
    sum_mul_lineDenom_eq α p M ε (sum_simplexPoint x) hdet t v]
  rfl

theorem shiftedConst_im (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    (shiftedConst α p M ε x v).im = -ε := by
  simp [shiftedConst]

theorem shiftedConst_re (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    (shiftedConst α p M ε x v).re =
      quadForm (symanzikMatrix α (simplexPoint x)) (v + spatialShift α p (simplexPoint x)) +
        symanzikV α p M (simplexPoint x) := by
  simp [shiftedConst]

/-! ### Continuity and measurability -/

theorem continuous_symanzikMatrix : Continuous fun z : Fin (m + 1) → ℝ => symanzikMatrix α z :=
  continuous_matrix fun s t => by
    simp only [symanzikMatrix, of_apply]
    fun_prop

theorem continuous_simplexPoint' : Continuous fun x : Fin m → ℝ => simplexPoint x :=
  continuous_pi fun i => continuous_simplexPoint i

theorem continuous_symanzikU_simplexPoint :
    Continuous fun x : Fin m → ℝ => symanzikU α (simplexPoint x) :=
  ((continuous_symanzikMatrix α).comp continuous_simplexPoint').matrix_det

theorem measurable_symanzikMatrix_inv :
    Measurable fun z : Fin (m + 1) → ℝ => (symanzikMatrix α z)⁻¹ := by
  refine Matrix.measurable_iff.mpr fun s t => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ((continuous_symanzikMatrix α).matrix_det.measurable.inv).mul
    ((continuous_symanzikMatrix α).matrix_adjugate.matrix_elem s t).measurable

theorem measurable_spatialShift :
    Measurable fun z : Fin (m + 1) → ℝ => spatialShift α p z := by
  refine measurable_pi_iff.mpr fun s => measurable_pi_iff.mpr fun c => ?_
  simp only [spatialShift, mulVec, dotProduct, coefVec]
  exact Finset.measurable_sum _ fun r _ =>
    (measurable_symanzikMatrix_inv α).eval_matrix.mul (by fun_prop)

theorem measurable_symanzikV : Measurable fun z : Fin (m + 1) → ℝ => symanzikV α p M z := by
  simp only [symanzikV, minkowski_dot_eq, symanzikVector]
  refine Measurable.sub (by fun_prop) (Finset.measurable_sum _ fun s _ =>
    Finset.measurable_sum _ fun t _ => (measurable_symanzikMatrix_inv α).eval_matrix.mul ?_)
  fun_prop

theorem continuous_quadForm_inv (hε : ε ≠ 0) :
    Continuous fun q : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → Fin 3 → ℝ) × ℝ =>
      ((((quadForm q.1 q.2.1 : ℝ) : ℂ) + (((q.2.2 : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹ := by
  refine Continuous.inv₀ ?_ fun q => pow_ne_zero _ fun h => ?_
  · simp only [Spatial.quadForm_eq_sum]
    fun_prop
  · have := congrArg Complex.im h
    simp at this
    exact hε this

theorem measurable_energyValue (hε : ε ≠ 0) :
    Measurable fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) => energyValue α p M ε q.1 q.2 := by
  have hZ := (continuous_simplexPoint' (m := m)).measurable
  have hA : Measurable fun x : Fin m → ℝ => symanzikMatrix α (simplexPoint x) :=
    (continuous_symanzikMatrix α).measurable.comp hZ
  have hσ := (measurable_spatialShift α p).comp hZ
  have hV := (measurable_symanzikV α p M).comp hZ
  have hΨ := (continuous_quadForm_inv (m := m) hε).measurable.comp
    ((hA.comp measurable_fst).prodMk (((measurable_snd).add (hσ.comp measurable_fst)).prodMk
      (hV.comp measurable_fst)))
  have hU : Measurable fun x : Fin m → ℝ =>
      ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ :=
    (continuous_ofReal.comp (continuous_symanzikU_simplexPoint α).sqrt).measurable.inv
  have : (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) => energyValue α p M ε q.1 q.2) =
      fun q => -(π / (((m + 1 : ℕ) : ℂ) - 1)) *
        ((Real.sqrt (symanzikU α (simplexPoint q.1)) : ℝ) : ℂ)⁻¹ *
        ((((quadForm (symanzikMatrix α (simplexPoint q.1))
          (q.2 + spatialShift α p (simplexPoint q.1)) : ℝ) : ℂ) +
          (((symanzikV α p M (simplexPoint q.1) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹ := by
    funext q
    simp only [energyValue, shiftedConst, Nat.add_sub_cancel]
  rw [this]
  exact (measurable_const.mul (hU.comp measurable_fst)).mul hΨ

theorem continuous_paramDenom (hε : ε ≠ 0) (v : Fin 2 → Fin 3 → ℝ) :
    Continuous fun q : (Fin m → ℝ) × (Fin 2 → ℝ) => (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹ := by
  refine Continuous.inv₀ (Continuous.pow ?_ _) fun q => pow_ne_zero _ fun h => ?_
  · have : (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) => paramDenom α p M ε q.1 q.2 v) =
        fun q => ∑ i, ((simplexPoint q.1 i : ℝ) : ℂ) *
          (((-(∑ s, α i s * q.2 s + p i 0) ^ 2 +
            ∑ c : Fin 3, (∑ s, α i s * v s c + p i c.succ) ^ 2 + M i ^ 2 : ℝ) : ℂ) -
              (ε : ℂ) * I) := by
      funext q
      rw [paramDenom, Feynman.simplexComb_eq_sum_simplexPoint]
      simp only [lineDenom_loopMomenta]
    rw [this]
    have hZ := continuous_simplexPoint' (m := m)
    fun_prop
  · have := paramDenom_im α p M (ε := ε) q.1 q.2 v
    rw [h, zero_im] at this
    exact hε (by linarith)

/-! ### Almost every point of the simplex is interior -/

theorem ae_posDef (hm : 0 < m) (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) :
    ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      x ∈ simplexSet m ∧ (symanzikMatrix α (simplexPoint x)).PosDef := by
  rw [ae_restrict_iff' (Feynman.measurableSet_simplexSet m)]
  filter_upwards [ae_simplexPoint_ne_zero hm] with x hx hxS
  refine ⟨hxS, posDef_symanzikMatrix α (fun i => ?_) hspan⟩
  exact lt_of_le_of_ne ((Feynman.simplexPoint_mem_stdSimplex hxS).1 i) (hx i).symm

theorem inv_sqrt_le_one_add_inv_sq (r : ℝ) : (Real.sqrt r)⁻¹ ≤ 1 + (r ^ 2)⁻¹ := by
  rcases le_or_gt r 0 with h | h
  · rw [Real.sqrt_eq_zero'.mpr h, _root_.inv_zero]
    positivity
  rcases le_or_gt r 1 with h1 | h1
  · have hs : r ^ 2 ≤ Real.sqrt r := by
      have : r ≤ Real.sqrt r := by
        rw [Real.le_sqrt h.le h.le]
        nlinarith
      nlinarith
    have : (Real.sqrt r)⁻¹ ≤ (r ^ 2)⁻¹ := inv_anti₀ (by positivity) hs
    linarith
  · have : 1 ≤ Real.sqrt r := by rw [Real.one_le_sqrt]; exact h1.le
    have : (Real.sqrt r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
    have : 0 ≤ (r ^ 2)⁻¹ := by positivity
    linarith

theorem integrableOn_inv_sqrt_symanzikU
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m)) :
    IntegrableOn (fun x => (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹) (simplexSet m) := by
  have : IsFiniteMeasure (volume.restrict (simplexSet m)) :=
    isFiniteMeasure_restrict.mpr (Feynman.isCompact_simplexSet m).measure_lt_top.ne
  refine ((integrable_const (1 : ℝ)).add hU).mono'
    ((continuous_symanzikU_simplexPoint α).sqrt.measurable.inv.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_sqrt_le_one_add_inv_sq _

/-! ### Fixed spatial momenta: Fubini on simplex × energies -/

/-- The bound `K(v)` on the real part of the shifted constant. -/
noncomputable def energyBound (v : Fin 2 → Fin 3 → ℝ) : ℝ :=
  ∑ i, (p i 0 ^ 2 + M i ^ 2 + ∑ c : Fin 3, (∑ s, α i s * v s c + p i c.succ) ^ 2)

theorem integrable_paramDenom (hm : 0 < m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹) (simplexSet m))
    (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) => (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume) := by
  have hmeas := (continuous_paramDenom α p M hε.ne' v).aestronglyMeasurable
    (μ := (volume.restrict (simplexSet m)).prod volume)
  have hK : 0 ≤ energyBound α p M v := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  have hn : 2 ≤ m + 1 := by omega
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_posDef α hm hspan] with x ⟨hxS, hPD⟩
    have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
    simp only [paramDenom_eq α p M hdet]
    exact integrable_inv_neg_shifted_quadratic_add_pow hPD
      (by rw [shiftedConst_im]; linarith) hn _
  · refine (hU.const_mul
      ((Real.sqrt δ ^ (m + 1))⁻¹ * energyNormConst (m + 1))).mono'
      hmeas.norm.integral_prod_right' ?_
    filter_upwards [ae_posDef α hm hspan] with x ⟨hxS, hPD⟩
    have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [paramDenom_eq α p M hdet]
    have hz := Feynman.simplexPoint_mem_stdSimplex hxS
    have hre : |(shiftedConst α p M ε x v).re| ≤ energyBound α p M v := by
      rw [shiftedConst_re]
      exact abs_re_shifted_le α p M hz.1 hz.2 hdet v
    refine (integral_norm_inv_neg_shifted_le hPD hre (shiftedConst_im α p M x v) hδ0 hδ hδε hn
      _).trans (le_of_eq ?_)
    unfold symanzikU
    ring

theorem integral_simplex_paramDenom (hm : 0 < m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) (v : Fin 2 → Fin 3 → ℝ) :
    ∫ x in simplexSet m, ∫ t : Fin 2 → ℝ, (paramDenom α p M ε x t v ^ (m + 1))⁻¹ =
      ∫ x in simplexSet m, energyValue α p M ε x v := by
  refine integral_congr_ae ?_
  filter_upwards [ae_posDef α hm hspan] with x ⟨hxS, hPD⟩
  have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
  simp only [paramDenom_eq α p M hdet]
  rw [integral_inv_neg_shifted_quadratic_add_pow hPD (by rw [shiftedConst_im]; linarith)
    (by omega : 2 ≤ m + 1)]
  rfl

/-- **Sub-step (a): the energy integral at fixed spatial momenta.** For `N = m + 1 ≥ 2`
propagators, `ε > 0`, two independent `αᵢ` and `U^{-1/2}` integrable on the simplex, the energy
integrand `∏ᵢ Dᵢ(t, v)⁻¹` is integrable and
`∫_{ℝ²} ∏ᵢ Dᵢ⁻¹ dt = m! ∫_Δ -(π/(N-1)) U^{-1/2} w^{1-N} dx`. -/
theorem integral_prod_lineDenom_eq (hm : 0 < m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹) (simplexSet m))
    (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun t : Fin 2 → ℝ => ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) ∧
      ∫ t : Fin 2 → ℝ, ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, energyValue α p M ε x v := by
  have hint := integrable_paramDenom α p M hm hε hspan hU v
  have hfey : ∀ t : Fin 2 → ℝ, ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
      (m.factorial : ℂ) * ∫ x in simplexSet m, (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
    intro t
    refine Feynman.prod_inv_eq_factorial_mul_integral_simplex fun i => ?_
    simp only [lineDenom, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      add_zero, zero_sub]
    linarith
  refine ⟨?_, ?_⟩
  · simp only [hfey]
    exact hint.integral_prod_right.const_mul _
  · simp only [hfey]
    rw [integral_const_mul, ← integral_simplex_paramDenom α p M hm hε hspan v]
    congr 1
    exact (integral_integral_swap
      (f := fun x t => (paramDenom α p M ε x t v ^ (m + 1))⁻¹) hint).symm

/-! ### Fubini on simplex × space -/

theorem integrable_energyValue (hm : 4 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m)) :
    Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) => energyValue α p M ε q.1 q.2)
      ((volume.restrict (simplexSet m)).prod volume) := by
  have hm0 : 0 < m := by omega
  have hmeas := (measurable_energyValue α p M hε.ne').aestronglyMeasurable
    (μ := (volume.restrict (simplexSet m)).prod volume)
  set K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2)
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  set c₀ : ℂ := -(π / (((m + 1 : ℕ) : ℂ) - 1))
  have hval : ∀ x v, energyValue α p M ε x v = c₀ *
      ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
      ((((quadForm (symanzikMatrix α (simplexPoint x))
        (v + spatialShift α p (simplexPoint x)) : ℝ) : ℂ) +
        (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹ := by
    intro x v
    simp only [energyValue, shiftedConst, Nat.add_sub_cancel, c₀]
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    simp only [hval]
    exact (integrable_inv_quadForm_shifted_add_pow hPD (by simp; linarith) hm _).const_mul _
  · set C : ℝ := ‖c₀‖ * ((Real.sqrt δ ^ m)⁻¹ *
      (π ^ 3 * (((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3))⁻¹))
    refine (hU.const_mul C).mono' hmeas.norm.integral_prod_right' ?_
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
    have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
    have hz := Feynman.simplexPoint_mem_stdSimplex hxS
    have hVb := abs_symanzikV_le α p M hz.1 hz.2 hdet
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [hval, norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [integral_const_mul]
    have hb := integral_norm_inv_quadForm_shifted_le hPD hVb hδ0 hδ hδε hm
      (spatialShift α p (simplexPoint x))
    simp only [norm_inv] at hb
    have hsq : Real.sqrt (symanzikU α (simplexPoint x)) ^ 4 =
        symanzikU α (simplexPoint x) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hUpos.le]
    have hspos : 0 < Real.sqrt (symanzikU α (simplexPoint x)) := Real.sqrt_pos.mpr hUpos
    calc ‖c₀‖ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ *
          ∫ v, (‖((((quadForm (symanzikMatrix α (simplexPoint x))
            (v + spatialShift α p (simplexPoint x)) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)‖)⁻¹
        ≤ ‖c₀‖ * (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ *
          ((Real.sqrt δ ^ m)⁻¹ * (π ^ 3 * (((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3))⁻¹ *
            (Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3)⁻¹)) := by
          gcongr
      _ = C * (symanzikU α (simplexPoint x) ^ 2)⁻¹ := by
          rw [← hsq]
          unfold symanzikU at hspos ⊢
          simp only [C]
          field_simp

/-! ### The parametric representation -/

/-- **The scalar two-loop parametric representation** (assembly of O2-10). For `N = m + 1 ≥ 5`
propagators with line momenta `kᵢ(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ`, masses `Mᵢ`, `ε > 0`, two linearly
independent `αᵢ`, and `U⁻²` integrable on the simplex (no divergent one-loop subintegration):
both stages of the joint energy-first integral of `∏ᵢ Dᵢ⁻¹`, `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε`, are
integrable, and
`jointEnergyFirstIntegral 2 (∏ᵢ Dᵢ⁻¹) = -π⁴ (N-5)! ∫_Δ U⁻² (V - iε)^{4-N} dx`,
with `Δ = simplexSet m`, `z = simplexPoint x`, `U = det A(z)` and `V = symanzikV`. -/
theorem jointEnergyFirstIntegral_prod_inv_lineDenom (hm : 4 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m)) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ =>
        ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ((m - 4).factorial : ℂ) *
        ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
          ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ := by
  have hm0 : 0 < m := by omega
  have hA := integral_prod_lineDenom_eq α p M hm0 hε hspan (integrableOn_inv_sqrt_symanzikU α hU)
  have hH := integrable_energyValue α p M hm hε hspan hU
  refine ⟨fun v => (hA v).1, ?_, ?_⟩
  · have : (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) =
        fun v => (m.factorial : ℂ) * ∫ x in simplexSet m, energyValue α p M ε x v :=
      funext fun v => (hA v).2
    rw [this]
    exact hH.integral_prod_right.const_mul _
  · -- the spatial integral at almost every simplex point
    have hspat : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
        ∫ v : Fin 2 → Fin 3 → ℝ, energyValue α p M ε x v =
          (-(π / (m : ℂ)) * ((π : ℂ) ^ 3 *
            (((m : ℂ) - 1) * ((m : ℂ) - 2) * ((m : ℂ) - 3))⁻¹)) *
          (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹) := by
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
      simp only [energyValue, shiftedConst, Nat.add_sub_cancel]
      rw [integral_const_mul, integral_inv_quadForm_shifted_add_pow hPD (by simp; linarith) hm]
      have hsq : Real.sqrt (symanzikU α (simplexPoint x)) ^ 4 =
          symanzikU α (simplexPoint x) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hUpos.le]
      have hspos : 0 < Real.sqrt (symanzikU α (simplexPoint x)) := Real.sqrt_pos.mpr hUpos
      rw [← hsq]
      unfold symanzikU at hspos ⊢
      have hs0 : ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det : ℝ) : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr hspos.ne'
      push_cast
      field_simp
      ring
    have hconst : (m.factorial : ℂ) * (-(π / (m : ℂ)) * ((π : ℂ) ^ 3 *
        (((m : ℂ) - 1) * ((m : ℂ) - 2) * ((m : ℂ) - 3))⁻¹)) =
        -((π : ℂ) ^ 4) * ((m - 4).factorial : ℂ) := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [Nat.add_sub_cancel, show (k + 4).factorial =
        (k + 4) * (k + 3) * (k + 2) * (k + 1) * k.factorial by simp only [Nat.factorial_succ]; ring]
      push_cast
      have e0 : (k : ℂ) + 4 ≠ 0 := by exact_mod_cast (by omega : k + 4 ≠ 0)
      have e1 : (k : ℂ) + 4 - 1 ≠ 0 := by
        rw [show (k : ℂ) + 4 - 1 = ((k + 3 : ℕ) : ℂ) by push_cast; ring]
        exact_mod_cast (by omega : k + 3 ≠ 0)
      have e2 : (k : ℂ) + 4 - 2 ≠ 0 := by
        rw [show (k : ℂ) + 4 - 2 = ((k + 2 : ℕ) : ℂ) by push_cast; ring]
        exact_mod_cast (by omega : k + 2 ≠ 0)
      have e3 : (k : ℂ) + 4 - 3 ≠ 0 := by
        rw [show (k : ℂ) + 4 - 3 = ((k + 1 : ℕ) : ℂ) by push_cast; ring]
        exact_mod_cast (by omega : k + 1 ≠ 0)
      field_simp
      ring
    have hA2 : ∀ v : Fin 2 → Fin 3 → ℝ, ∫ t : Fin 2 → ℝ,
        ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
          (m.factorial : ℂ) * ∫ x in simplexSet m, energyValue α p M ε x v := fun v => (hA v).2
    show ∫ v : Fin 2 → Fin 3 → ℝ, ∫ t : Fin 2 → ℝ,
        ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ = _
    simp only [hA2]
    rw [integral_const_mul, ← integral_integral_swap
      (f := fun x v => energyValue α p M ε x v) hH, integral_congr_ae hspat,
      integral_const_mul, ← mul_assoc, hconst]

end QED.Integration.TwoLoop

end
