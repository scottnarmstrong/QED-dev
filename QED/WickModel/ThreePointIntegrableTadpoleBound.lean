/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassification
import QED.WickModel.VacuumPolarizationBounds
import QED.WickModel.VacuumPolarizationAlgebra
import QED.WickModel.VacuumPolarizationEnergyFirst
import QED.Integration.LoopBounds
import QED.OneLoop.VertexAlgebra
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Pauli–Villars sum of a tadpole loop

A tadpole is a one-vertex closed fermion loop. Summed over the regulator flavors, its loop
factor is built from the off-diagonal entries of `∑_f c_f S̃_f(ℓ)`, that is from
`ℓ^ν ∑_f c_f (ℓ² + M_f² - iε)⁻¹`. A single flavor decays only like `|ℓ|⁻¹`; the Pauli–Villars
conditions make both stages of the energy-first prescription M1 integrable at every `ε > 0`:

* in the loop energy: `∑ c_f = 0` turns the flavor sum into `∑_f c_f (m² - M_f²) D_f⁻¹ D_0⁻¹`,
  which decays like `t⁻⁴`; the spatial components are integrable flavor by flavor;
* over the spatial momentum: the time component integrates to `0` by oddness, and for the
  spatial components the energy integral is `-π ∑_f c_f (-(|v|² + M_f²) + iε)^{-1/2}`, which
  decays like `|v|⁻⁵` by the second-order Pauli–Villars cancellation
  (`VacuumPolarizationLimit.norm_sum_cpow_le_two`), using also `∑ c_f M_f² = 0`.

## Main statements

* `TadpoleBound.integrableEnergyFirst_coord_mul_pvSum`: `ℓ ↦ ℓ^ν ∑_f c_f (ℓ² + M_f² - iε)⁻¹`
  is integrable in both stages.
* `TadpoleBound.integrableEnergyFirst_sum_electronPropagator`: so is each off-diagonal entry of
  `∑_f c_f S̃_f(ℓ)`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Complex MeasureTheory Filter Set
open scoped Real

namespace QED.WickModel

namespace TadpoleBound

/-- The Pauli–Villars sum `∑_f c_f (ℓ² + M_f² - iε)⁻¹`. -/
noncomputable def pvSum (P : Params) (ε : ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
    (((Minkowski.dot ℓ ℓ + P.mass f ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹

/-- The denominator `-t² + W - iε` at loop energy `t`. -/
noncomputable def den (ε W t : ℝ) : ℂ :=
  ((-t ^ 2 + W : ℝ) : ℂ) - (ε : ℂ) * I

/-- The Minkowski square in the energy-first coordinates. -/
theorem dot_cons (t : ℝ) (v : Fin 3 → ℝ) :
    Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) = -t ^ 2 + ∑ k, v k ^ 2 := by
  simpa using QED.OneLoop.dot_cons_add t v 0

/-- The Pauli–Villars sum in the energy-first coordinates. -/
theorem pvSum_cons (P : Params) (ε t : ℝ) (v : Fin 3 → ℝ) :
    pvSum P ε (Fin.cons t v) =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) * (den ε (∑ k, v k ^ 2 + P.mass f ^ 2) t)⁻¹ := by
  simp only [pvSum, den, dot_cons, add_assoc]

/-- The imaginary part of the denominator is `-ε`. -/
theorem den_im (ε W t : ℝ) : (den ε W t).im = -ε := by
  simp only [den, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
  ring

/-- The denominator does not vanish for `ε ≠ 0`. -/
theorem den_ne_zero {ε : ℝ} (hε : ε ≠ 0) (W t : ℝ) : den ε W t ≠ 0 := by
  intro h
  have him := den_im ε W t
  rw [h, zero_im] at him
  exact hε (by linarith)

/-- `-X + iε` lies in the slit plane for `ε > 0`. -/
theorem neg_add_mul_I_mem_slitPlane {ε : ℝ} (hε : 0 < ε) (X : ℝ) :
    -(X : ℂ) + ε * I ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simp only [add_im, neg_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
  intro h
  linarith

/-- The denominator is even in the loop energy. -/
theorem den_neg (ε W t : ℝ) : den ε W (-t) = den ε W t := by
  simp [den]

/-- The denominator is continuous in the loop energy. -/
theorem continuous_den (ε W : ℝ) : Continuous (den ε W) := by
  unfold den
  fun_prop

/-- The denominator grows like `1 + t²`. -/
theorem exists_mul_le_norm_den {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    ∃ c > 0, ∀ t : ℝ, c * (1 + t ^ 2) ≤ ‖den ε W t‖ := by
  obtain ⟨c, hc, h⟩ := QED.Integration.exists_mul_one_add_sq_le_norm hε 0 W
  refine ⟨c, hc, fun t => ?_⟩
  have h' := h t 0 W (by simp) le_rfl
  have e : -((t : ℂ) + ((0 : ℝ) : ℂ)) ^ 2 + (W : ℂ) - (ε : ℂ) * I = den ε W t := by
    simp only [den]
    push_cast
    ring
  rwa [e] at h'

/-- `‖(-t² + W - iε)⁻¹‖ ≤ c⁻¹ (1 + t²)⁻¹`. -/
theorem norm_inv_den_le {ε c W : ℝ} (hc : 0 < c) (h : ∀ t : ℝ, c * (1 + t ^ 2) ≤ ‖den ε W t‖)
    (t : ℝ) : ‖(den ε W t)⁻¹‖ ≤ c⁻¹ * (1 + t ^ 2)⁻¹ := by
  rw [norm_inv, ← mul_inv]
  exact inv_anti₀ (by positivity) (h t)

/-- The inverse denominator is integrable in the loop energy. -/
theorem integrable_inv_den {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    Integrable fun t : ℝ => (den ε W t)⁻¹ := by
  obtain ⟨c, hc, h⟩ := exists_mul_le_norm_den hε W
  refine (integrable_inv_one_add_sq.const_mul c⁻¹).mono'
    ((continuous_den ε W).inv₀ (den_ne_zero hε.ne' W)).aestronglyMeasurable
    (Eventually.of_forall fun t => norm_inv_den_le hc h t)

/-- `t (-t² + W - iε)⁻¹ (-t² + W' - iε)⁻¹` is integrable in the loop energy. -/
theorem integrable_mul_inv_den_mul_inv_den {ε : ℝ} (hε : 0 < ε) (W W' : ℝ) :
    Integrable fun t : ℝ => (t : ℂ) * (den ε W t)⁻¹ * (den ε W' t)⁻¹ := by
  obtain ⟨c, hc, h⟩ := exists_mul_le_norm_den hε W
  obtain ⟨c', hc', h'⟩ := exists_mul_le_norm_den hε W'
  refine (integrable_inv_one_add_sq.const_mul (c⁻¹ * c'⁻¹)).mono'
    (((continuous_ofReal.mul ((continuous_den ε W).inv₀ (den_ne_zero hε.ne' W))).mul
      ((continuous_den ε W').inv₀ (den_ne_zero hε.ne' W'))).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  have h1 := norm_inv_den_le hc h t
  have h2 := norm_inv_den_le hc' h' t
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1)]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |t| * ‖(den ε W t)⁻¹‖ * ‖(den ε W' t)⁻¹‖
      ≤ (1 + t ^ 2) * (c⁻¹ * (1 + t ^ 2)⁻¹) * (c'⁻¹ * (1 + t ^ 2)⁻¹) := by
        gcongr
    _ = c⁻¹ * c'⁻¹ * (1 + t ^ 2)⁻¹ := by
        field_simp

/-- `∫ (-t² + W - iε)⁻¹ dt = -π (-W + iε)^{-1/2}` for `ε > 0`. -/
theorem integral_inv_den {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    ∫ t : ℝ, (den ε W t)⁻¹ = -(π * (-(W : ℂ) + ε * I) ^ (-((1 / 2 : ℝ) : ℂ))) := by
  have hz : -(W : ℂ) + ε * I ∈ slitPlane := neg_add_mul_I_mem_slitPlane hε W
  have hpt : ∀ t : ℝ, (den ε W t)⁻¹ = -(((t : ℂ) ^ 2 + (-(W : ℂ) + ε * I)) ^ (-1 : ℤ)) := by
    intro t
    rw [zpow_neg_one, ← inv_neg]
    congr 1
    simp only [den]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_neg, VacuumPolarizationLimit.integral_sq_add_zpow_one hz]
  congr 3
  push_cast
  ring

/-! ### The time component -/

/-- **Flavor collapse in the loop energy.** With `∑ c_f = 0`,
`∑_f c_f D_f⁻¹ = ∑_f c_f (D_0 - D_f) D_f⁻¹ D_0⁻¹`. -/
theorem sum_mul_inv_eq {c : Fin 3 → ℂ} (hc : ∑ f, c f = 0) {z : Fin 3 → ℂ}
    (hz : ∀ f, z f ≠ 0) :
    ∑ f, c f * (z f)⁻¹ = ∑ f, c f * (z 0 - z f) * (z f)⁻¹ * (z 0)⁻¹ := by
  have hterm : ∀ f, c f * (z 0 - z f) * (z f)⁻¹ * (z 0)⁻¹ = c f * (z f)⁻¹ - c f * (z 0)⁻¹ := by
    intro f
    field_simp [hz f, hz 0]
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, hc, zero_mul, sub_zero]

/-- The difference of two denominators. -/
theorem den_sub_den (ε W W' t : ℝ) : den ε W t - den ε W' t = ((W - W' : ℝ) : ℂ) := by
  simp only [den]
  push_cast
  ring

/-- The time component of the tadpole sum, rewritten with the flavor collapse. -/
theorem mul_pvSum_cons_eq {P : Params} (hPV₁ : 1 + P.c₁ + P.c₂ = 0) {ε : ℝ} (hε : ε ≠ 0)
    (t : ℝ) (v : Fin 3 → ℝ) :
    (t : ℂ) * pvSum P ε (Fin.cons t v) =
      ∑ f : Fin 3, ((P.loopCoeff f * (P.mass 0 ^ 2 - P.mass f ^ 2) : ℝ) : ℂ) *
        ((t : ℂ) * (den ε (∑ k, v k ^ 2 + P.mass f ^ 2) t)⁻¹ *
          (den ε (∑ k, v k ^ 2 + P.mass 0 ^ 2) t)⁻¹) := by
  have hc : ∑ f, (P.loopCoeff f : ℂ) = 0 := by
    have := VacuumPolarizationLimit.sum_loopCoeff hPV₁
    exact_mod_cast this
  rw [pvSum_cons, sum_mul_inv_eq (z := fun f => den ε (∑ k, v k ^ 2 + P.mass f ^ 2) t) hc
    (fun f => den_ne_zero hε _ t), Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [den_sub_den]
  push_cast
  ring

/-- **The time component is integrable in the loop energy** (`∑ c_f = 0`, `ε > 0`). -/
theorem integrable_time {P : Params} (hPV₁ : 1 + P.c₁ + P.c₂ = 0) {ε : ℝ} (hε : 0 < ε)
    (v : Fin 3 → ℝ) : Integrable fun t : ℝ => (t : ℂ) * pvSum P ε (Fin.cons t v) := by
  simp_rw [mul_pvSum_cons_eq hPV₁ hε.ne']
  exact integrable_finsetSum _ fun f _ =>
    (integrable_mul_inv_den_mul_inv_den hε _ _).const_mul _

/-- The Pauli–Villars sum is even in the loop energy. -/
theorem pvSum_cons_neg (P : Params) (ε t : ℝ) (v : Fin 3 → ℝ) :
    pvSum P ε (Fin.cons (-t) v) = pvSum P ε (Fin.cons t v) := by
  simp only [pvSum_cons, den_neg]

/-- **The energy integral of the time component vanishes**: the integrand is odd. -/
theorem integral_time (P : Params) (ε : ℝ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, (t : ℂ) * pvSum P ε (Fin.cons t v) = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => (t : ℂ) * pvSum P ε (Fin.cons t v)) volume
  simp only [pvSum_cons_neg, ofReal_neg, neg_mul, integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-! ### The spatial components -/

/-- **The Pauli–Villars sum is integrable in the loop energy** (`ε > 0`). -/
theorem integrable_space (P : Params) {ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => pvSum P ε (Fin.cons t v) := by
  simp_rw [pvSum_cons]
  exact integrable_finsetSum _ fun f _ => (integrable_inv_den hε _).const_mul _

/-- The closed form of the energy integral: `∑_f c_f (-(|v|² + M_f²) + iε)^{-1/2}`. -/
noncomputable def closedForm (P : Params) (ε : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
    (-((∑ k, v k ^ 2 + P.mass f ^ 2 : ℝ) : ℂ) + ε * I) ^ (-((1 / 2 : ℝ) : ℂ))

/-- **The energy integral of the Pauli–Villars sum**: `-π` times the closed form. -/
theorem integral_space (P : Params) {ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, pvSum P ε (Fin.cons t v) = -(π * closedForm P ε v) := by
  simp_rw [pvSum_cons]
  rw [integral_finsetSum _ fun f _ => (integrable_inv_den hε _).const_mul _]
  simp only [integral_const_mul, integral_inv_den hε, closedForm, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-- The closed form is continuous in the spatial momentum. -/
theorem continuous_closedForm (P : Params) {ε : ℝ} (hε : 0 < ε) :
    Continuous (closedForm P ε) := by
  unfold closedForm
  refine continuous_finsetSum _ fun f _ => continuous_const.mul ?_
  exact Continuous.cpow (by fun_prop) continuous_const fun v =>
    neg_add_mul_I_mem_slitPlane hε _

/-- **The second-order Pauli–Villars bound on the closed form**: it decays like `|v|⁻⁵`. -/
theorem exists_norm_closedForm_le {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ v : Fin 3 → ℝ, ‖closedForm P ε v‖ ≤ K * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  have hm2 : 0 < P.mass 0 ^ 2 := by
    have : P.mass 0 = P.m := rfl
    rw [this]
    positivity
  obtain ⟨c, hc, hcoer⟩ := QED.Integration.exists_mul_one_add_norm_sq_le (n := 3) 0 hm2
  set A : ℝ := ∑ f : Fin 3, |P.loopCoeff f| * (P.mass f ^ 2 - P.mass 0 ^ 2) ^ 2
  refine ⟨(1 / 2) * (1 / 2 + 1) * A * c ^ (-(1 / 2 + 2 : ℝ)), fun v => ?_⟩
  set W : Fin 3 → ℝ := fun f => ∑ k, v k ^ 2 + P.mass f ^ 2 with hW
  have hsum : ∑ f, P.loopCoeff f = 0 := VacuumPolarizationLimit.sum_loopCoeff hPV₁
  have hsumW : ∑ f, P.loopCoeff f * W f = 0 := by
    have h2 := VacuumPolarizationLimit.sum_loopCoeff_mul_mass_sq hPV₂
    simp only [hW, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_add]
    rw [← h2]
  have hWle : ∀ f, W 0 ≤ W f := fun f => by
    simp only [hW]
    linarith [VacuumPolarizationLimit.mass_sq_le hm hM₁ hM₂ f]
  have hbound := VacuumPolarizationLimit.norm_sum_cpow_le_two hε (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hsum hsumW hWle
  have hA : ∑ f, |P.loopCoeff f| * (W f - W 0) ^ 2 = A := by
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [hW]
    ring
  rw [hA] at hbound
  have hlow : c * (1 + ‖v‖) ^ 2 ≤ max ε (W 0) := by
    have := hcoer v 0 (P.mass 0 ^ 2) (by simp) le_rfl
    simp only [Pi.zero_apply, add_zero] at this
    exact this.trans (le_max_right _ _)
  have hrpow := VacuumPolarizationLimit.rpow_neg_le_of_mul_sq_le hc (by positivity) hlow
    (by norm_num : (0 : ℝ) ≤ 1 / 2 + 2)
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun f _ => by positivity
  calc ‖closedForm P ε v‖ ≤ 1 / 2 * (1 / 2 + 1) * A * max ε (W 0) ^ (-(1 / 2 + 2 : ℝ)) :=
        hbound
    _ ≤ 1 / 2 * (1 / 2 + 1) * A * (c ^ (-(1 / 2 + 2 : ℝ)) *
          (1 + ‖v‖) ^ (-(2 * (1 / 2 + 2) : ℝ))) := by gcongr
    _ = _ := by
        rw [show -(2 * (1 / 2 + 2) : ℝ) = -5 by norm_num]
        ring

/-- **The energy integral of a spatial component is integrable over the spatial momentum.** -/
theorem integrable_integral_space {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    (k : Fin 3) :
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, (v k : ℂ) * pvSum P ε (Fin.cons t v) := by
  obtain ⟨K, hK⟩ := exists_norm_closedForm_le hm hM₁ hM₂ hPV₁ hPV₂ hε
  have hint : Integrable fun v : Fin 3 → ℝ => (v k : ℂ) * -(π * closedForm P ε v) := by
    refine ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 4)
      (by simp; norm_num)).const_mul (π * K)).mono'
      (((continuous_ofReal.comp (continuous_apply k)).mul
        (continuous_const.mul (continuous_closedForm P hε)).neg).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    have hv : |v k| ≤ 1 + ‖v‖ := by
      have := norm_le_pi_norm v k
      rw [Real.norm_eq_abs] at this
      linarith [norm_nonneg v]
    have hpos : 0 < 1 + ‖v‖ := by positivity
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hsplit : (1 + ‖v‖) ^ (-(4 : ℝ)) = (1 + ‖v‖) ^ (-(5 : ℝ)) * (1 + ‖v‖) := by
      rw [show -(4 : ℝ) = -5 + 1 by norm_num, Real.rpow_add hpos, Real.rpow_one]
    rw [hsplit]
    have hK0 : 0 ≤ K * (1 + ‖v‖) ^ (-(5 : ℝ)) := (norm_nonneg _).trans (hK v)
    calc |v k| * (π * ‖closedForm P ε v‖)
        ≤ (1 + ‖v‖) * (π * (K * (1 + ‖v‖) ^ (-(5 : ℝ)))) := by
          gcongr
          exact hK v
      _ = π * K * ((1 + ‖v‖) ^ (-(5 : ℝ)) * (1 + ‖v‖)) := by ring
  refine hint.congr (Eventually.of_forall fun v => ?_)
  simp only
  rw [integral_const_mul, integral_space P hε]

/-! ### Both stages -/

/-- **Each component of `ℓ ↦ ℓ^ν ∑_f c_f (ℓ² + M_f² - iε)⁻¹` is integrable in both stages of
the energy-first prescription**, for `ε > 0`, regulator fermions heavier than the electron, and
the Pauli–Villars conditions. -/
theorem integrableEnergyFirst_coord_mul_pvSum {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    (ν : Fin 4) : IntegrableEnergyFirst fun ℓ => (ℓ ν : ℂ) * pvSum P ε ℓ := by
  refine Fin.cases ?_ (fun k => ?_) ν
  · refine ⟨fun v => ?_, ?_⟩
    · simpa only [Fin.cons_zero] using integrable_time hPV₁ hε v
    · simp only [Fin.cons_zero, integral_time]
      exact integrable_zero _ _ _
  · refine ⟨fun v => ?_, ?_⟩
    · simpa only [Fin.cons_succ] using (integrable_space P hε v).const_mul (v k : ℂ)
    · simpa only [Fin.cons_succ] using integrable_integral_space hm hM₁ hM₂ hPV₁ hPV₂ hε k

/-- The off-diagonal entries of the flavor sum of electron propagators. -/
theorem sum_electronPropagator_apply_of_ne (P : Params) (ε : ℝ) (ℓ : Fin 4 → ℝ) {i j : Fin 4}
    (hij : i ≠ j) :
    ∑ f : Fin 3, (P.loopCoeff f : ℂ) * QED.OneLoop.electronPropagator (P.mass f) ε ℓ i j =
      ∑ μ, ∑ ν, (-((Minkowski.metric μ ν : ℝ) : ℂ) * Dirac.gamma μ i j) *
        ((ℓ ν : ℂ) * pvSum P ε ℓ) := by
  have h1 : ∀ f : Fin 3, QED.OneLoop.electronPropagator (P.mass f) ε ℓ i j =
      (((Minkowski.dot ℓ ℓ + P.mass f ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * -(Dirac.slash ℓ i j) := by
    intro f
    simp [QED.OneLoop.electronPropagator, Matrix.one_apply_ne hij]
  have h2 : Dirac.slash ℓ i j =
      ∑ μ, ∑ ν, ((Minkowski.metric μ ν : ℝ) : ℂ) * Dirac.gamma μ i j * (ℓ ν : ℂ) := by
    simp only [Dirac.slash, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Minkowski.lower,
      ofReal_sum, ofReal_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  have h3 : ∑ f : Fin 3, (P.loopCoeff f : ℂ) * QED.OneLoop.electronPropagator (P.mass f) ε ℓ i j =
      -(Dirac.slash ℓ i j) * pvSum P ε ℓ := by
    simp only [h1, pvSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  rw [h3, h2, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun ν _ => by ring

/-- **Each off-diagonal entry of `∑_f c_f S̃_f(ℓ)` is integrable in both stages of the
energy-first prescription**, for `ε > 0`, regulator fermions heavier than the electron, and the
Pauli–Villars conditions. -/
theorem integrableEnergyFirst_sum_electronPropagator {P : Params} (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    {i j : Fin 4} (hij : i ≠ j) :
    IntegrableEnergyFirst fun ℓ =>
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) * QED.OneLoop.electronPropagator (P.mass f) ε ℓ i j := by
  simp only [sum_electronPropagator_apply_of_ne P ε _ hij]
  exact IntegrableEnergyFirst.finsetSum _ fun μ _ => IntegrableEnergyFirst.finsetSum _ fun ν _ =>
    (integrableEnergyFirst_coord_mul_pvSum hm hM₁ hM₂ hPV₁ hPV₂ hε ν).const_mul _

end TadpoleBound

end QED.WickModel

end
