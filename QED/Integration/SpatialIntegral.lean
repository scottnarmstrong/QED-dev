/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import QED.Integration.LoopBounds

/-!
# Spatial loop integrals in three dimensions

After the loop-energy integral, the one-loop vertex reduces to integrals over the spatial loop
momentum `v : Fin 3 → ℝ` of functions of the Euclidean square `∑ k, v k ^ 2` (note that `‖v‖`
is the sup norm on `Fin 3 → ℝ`). This module evaluates the two radial integrals needed for the
Pauli–Villars-paired vertex in closed form and records the symmetry identities that reduce
tensor numerators to radial ones.

## Main statements

* `QED.Integration.integrable_sum_sq_add_rpow`: `(|v|² + D)^{-s}` is integrable on `ℝ³` for
  `s > 3/2`.
* `QED.Integration.integral_sum_sq_add_rpow_neg_five_halves`:
  `∫_{ℝ³} (|v|² + D)^{-5/2} d³v = 4π/(3D)`.
* `QED.Integration.integrable_sum_sq_add_rpow_neg_three_halves_sub` and
  `QED.Integration.integral_sum_sq_add_rpow_neg_three_halves_sub`: the Pauli–Villars-paired
  logarithmic integral `∫_{ℝ³} [(|v|² + D₁)^{-3/2} - (|v|² + D₂)^{-3/2}] d³v = 2π log(D₂/D₁)`.
* `QED.Integration.integral_coord_smul_radial` and
  `QED.Integration.integral_coord_mul_coord_smul_radial`: odd and mixed moments of radial
  functions vanish.
* `QED.Integration.integral_coord_sq_smul_radial`: isotropy of second moments,
  `∫ v_k² g(|v|²) = (1/3) ∫ |v|² g(|v|²)`.

## Implementation notes

The radial integrals are computed in spherical coordinates: `Fin 3 → ℝ` is identified with
`EuclideanSpace ℝ (Fin 3)` by a volume-preserving equivalence, where `‖x‖² = ∑ k, x k ^ 2`, and
`MeasureTheory.integral_fun_norm_addHaar` together with the volume `4π/3` of the unit ball
reduces them to integrals over `(0, ∞)`. These are evaluated with explicit antiderivatives,
`r³ / (3D (r² + D)^{3/2})` for `r² (r² + D)^{-5/2}` and `log (r + √(r² + D)) - r / √(r² + D)`
for `r² (r² + D)^{-3/2}`. The symmetry identities use the volume-preserving maps `v ↦ -v`, a
reflection of one coordinate, and a transposition of two coordinates.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace QED.Integration

/-! ### Reduction to radial integrals -/

/-- Spherical coordinates for functions of the Euclidean square on `ℝ³`:
`∫_{ℝ³} h(|v|²) d³v = 4π ∫₀^∞ r² h(r²) dr`. -/
theorem integral_comp_sum_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) :
    ∫ v : Fin 3 → ℝ, h (∑ k, v k ^ 2) = (4 * π) • ∫ r in Ioi (0 : ℝ), r ^ 2 • h (r ^ 2) := by
  have e := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun v : Fin 3 → ℝ => h (∑ k, v k ^ 2))
  rw [← e]
  have h2 : ∀ x : EuclideanSpace ℝ (Fin 3),
      ∑ k, ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm x) k ^ 2 = ‖x‖ ^ 2 := fun x => by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  simp_rw [h2]
  rw [integral_fun_norm_addHaar volume (fun r => h (r ^ 2))]
  simp only [finrank_euclideanSpace_fin, measureReal_def, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (by positivity),
    show 3 - 1 = 2 from rfl, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  push_cast
  ring

/-- Integrability of functions of the Euclidean square on `ℝ³` reduces to integrability of
`r² h(r²)` on `(0, ∞)`. -/
theorem integrable_comp_sum_sq_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) :
    Integrable (fun v : Fin 3 → ℝ => h (∑ k, v k ^ 2)) ↔
      IntegrableOn (fun r : ℝ => r ^ 2 • h (r ^ 2)) (Ioi 0) := by
  have e := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (g := fun v : Fin 3 → ℝ => h (∑ k, v k ^ 2))
  rw [← e]
  have h2 : ∀ x : EuclideanSpace ℝ (Fin 3),
      ∑ k, ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm x) k ^ 2 = ‖x‖ ^ 2 := fun x => by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  simp only [Function.comp_def, h2]
  have := integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (f := fun r => h (r ^ 2))
  rw [finrank_euclideanSpace_fin] at this
  exact this

/-! ### One-variable radial integrals -/

/-- `x^{-3/2} = (√x)⁻³` for `x ≥ 0`. -/
theorem rpow_neg_three_halves_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(3 / 2 : ℝ)) = ((√x) ^ 3)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_neg hx]
  norm_num

/-- `x^{-5/2} = (√x)⁻⁵` for `x ≥ 0`. -/
theorem rpow_neg_five_halves_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(5 / 2 : ℝ)) = ((√x) ^ 5)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_neg hx]
  norm_num

/-- The derivative of `√(r² + D)` is `r / √(r² + D)`. -/
theorem hasDerivAt_sqrt_sq_add {D : ℝ} (hD : 0 < D) (r : ℝ) :
    HasDerivAt (fun r : ℝ => √(r ^ 2 + D)) (r / √(r ^ 2 + D)) r := by
  have h := ((hasDerivAt_pow 2 r).add_const D).sqrt (by positivity)
  refine h.congr_deriv ?_
  have : 0 < √(r ^ 2 + D) := Real.sqrt_pos.2 (by positivity)
  field_simp
  push_cast
  ring

/-- `r / √(r² + D) → 1` as `r → ∞`. -/
theorem tendsto_div_sqrt_sq_add_atTop {D : ℝ} (hD : 0 ≤ D) :
    Tendsto (fun r : ℝ => r / √(r ^ 2 + D)) atTop (𝓝 1) := by
  have hψ : Tendsto (fun u : ℝ => (√(1 + D * u ^ 2))⁻¹) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun u : ℝ => √(1 + D * u ^ 2) := by fun_prop
    simpa using (hc.tendsto 0).inv₀ (by simp)
  refine (hψ.comp tendsto_inv_atTop_zero).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have h1 : r ^ 2 + D = r ^ 2 * (1 + D * r⁻¹ ^ 2) := by field_simp
  rw [Function.comp_apply, h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
  have : 0 < √(1 + D * r⁻¹ ^ 2) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- `∫₀^∞ r² (r² + D)^{-5/2} dr = 1/(3D)`. -/
theorem integral_Ioi_sq_mul_rpow_neg_five_halves {D : ℝ} (hD : 0 < D) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (r ^ 2 + D) ^ (-(5 / 2 : ℝ)) = 1 / (3 * D) := by
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ => (r / √(r ^ 2 + D)) ^ 3 / (3 * D))
      (r ^ 2 * (r ^ 2 + D) ^ (-(5 / 2 : ℝ))) r := by
    intro r _
    have hS : 0 < √(r ^ 2 + D) := Real.sqrt_pos.2 (by positivity)
    have hS2 : √(r ^ 2 + D) ^ 2 = r ^ 2 + D := Real.sq_sqrt (by positivity)
    have h := (((hasDerivAt_id r).div (hasDerivAt_sqrt_sq_add hD r) hS.ne').pow 3).div_const
      (3 * D)
    refine h.congr_deriv ?_
    rw [rpow_neg_five_halves_eq (by positivity)]
    simp only [Pi.div_apply, id, Nat.cast_ofNat, show 3 - 1 = 2 from rfl]
    generalize √(r ^ 2 + D) = S at hS hS2 ⊢
    field_simp
    linear_combination r ^ 2 * hS2
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r ^ 2 * (r ^ 2 + D) ^ (-(5 / 2 : ℝ)) := fun r _ => by
    positivity
  have hlim : Tendsto (fun r : ℝ => (r / √(r ^ 2 + D)) ^ 3 / (3 * D)) atTop
      (𝓝 (1 ^ 3 / (3 * D))) := ((tendsto_div_sqrt_sq_add_atTop hD.le).pow 3).div_const _
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  simp

/-- An antiderivative of `r² (r² + D)^{-3/2}` on `[0, ∞)`:
`log (r + √(r² + D)) - r / √(r² + D)`. -/
theorem hasDerivAt_log_add_sqrt_sub_div {D : ℝ} (hD : 0 < D) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun r : ℝ => Real.log (r + √(r ^ 2 + D)) - r / √(r ^ 2 + D))
      (r ^ 2 * (r ^ 2 + D) ^ (-(3 / 2 : ℝ))) r := by
  have hS : 0 < √(r ^ 2 + D) := Real.sqrt_pos.2 (by positivity)
  have hrS : 0 < r + √(r ^ 2 + D) := by positivity
  have h := (((hasDerivAt_id r).add (hasDerivAt_sqrt_sq_add hD r)).log hrS.ne').sub
    ((hasDerivAt_id r).div (hasDerivAt_sqrt_sq_add hD r) hS.ne')
  refine h.congr_deriv ?_
  rw [rpow_neg_three_halves_eq (by positivity)]
  simp only [id, Pi.add_apply]
  generalize √(r ^ 2 + D) = S at hS hrS ⊢
  field_simp
  ring

/-- `(r + √(r² + D₁)) / (r + √(r² + D₂)) → 1` as `r → ∞`. -/
theorem tendsto_add_sqrt_div_add_sqrt_atTop {D₁ D₂ : ℝ} (h₁ : 0 ≤ D₁) (h₂ : 0 ≤ D₂) :
    Tendsto (fun r : ℝ => (r + √(r ^ 2 + D₁)) / (r + √(r ^ 2 + D₂))) atTop (𝓝 1) := by
  have h := (((tendsto_div_sqrt_sq_add_atTop h₁).inv₀ one_ne_zero).const_add 1).div
    (((tendsto_div_sqrt_sq_add_atTop h₂).inv₀ one_ne_zero).const_add 1) (by norm_num)
  rw [show ((1 : ℝ) + 1⁻¹) / (1 + 1⁻¹) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hS₁ : 0 < √(r ^ 2 + D₁) := Real.sqrt_pos.2 (by positivity)
  have hS₂ : 0 < √(r ^ 2 + D₂) := Real.sqrt_pos.2 (by positivity)
  simp only [Pi.div_apply]
  field_simp

/-- The difference of the antiderivatives for `D₁` and `D₂` tends to `0` at infinity. -/
theorem tendsto_log_add_sqrt_sub_div_sub_atTop {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    Tendsto (fun r : ℝ => (Real.log (r + √(r ^ 2 + D₁)) - r / √(r ^ 2 + D₁))
      - (Real.log (r + √(r ^ 2 + D₂)) - r / √(r ^ 2 + D₂))) atTop (𝓝 0) := by
  have hlog := (tendsto_add_sqrt_div_add_sqrt_atTop h₁.le h₂.le).log one_ne_zero
  rw [Real.log_one] at hlog
  have h := hlog.sub
    ((tendsto_div_sqrt_sq_add_atTop h₁.le).sub (tendsto_div_sqrt_sq_add_atTop h₂.le))
  rw [sub_self, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hS₁ : 0 < r + √(r ^ 2 + D₁) := by positivity
  have hS₂ : 0 < r + √(r ^ 2 + D₂) := by positivity
  rw [Real.log_div hS₁.ne' hS₂.ne']
  ring

/-- An antiderivative of the Pauli–Villars-paired radial integrand on `[0, ∞)`. -/
theorem hasDerivAt_log_add_sqrt_sub_div_sub {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) {r : ℝ}
    (hr : 0 ≤ r) :
    HasDerivAt (fun r : ℝ => (Real.log (r + √(r ^ 2 + D₁)) - r / √(r ^ 2 + D₁))
        - (Real.log (r + √(r ^ 2 + D₂)) - r / √(r ^ 2 + D₂)))
      (r ^ 2 * ((r ^ 2 + D₁) ^ (-(3 / 2 : ℝ)) - (r ^ 2 + D₂) ^ (-(3 / 2 : ℝ)))) r :=
  ((hasDerivAt_log_add_sqrt_sub_div h₁ hr).sub
    (hasDerivAt_log_add_sqrt_sub_div h₂ hr)).congr_deriv (mul_sub _ _ _).symm

/-- The Pauli–Villars-paired radial integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_sq_mul_rpow_neg_three_halves_sub {D₁ D₂ : ℝ} (h₁ : 0 < D₁)
    (h₂ : 0 < D₂) :
    IntegrableOn
      (fun r : ℝ => r ^ 2 * ((r ^ 2 + D₁) ^ (-(3 / 2 : ℝ)) - (r ^ 2 + D₂) ^ (-(3 / 2 : ℝ))))
      (Ioi 0) := by
  have hd : ∀ r ∈ Ici (0 : ℝ), _ := fun r (hr : 0 ≤ r) =>
    hasDerivAt_log_add_sqrt_sub_div_sub h₁ h₂ hr
  rcases le_total D₁ D₂ with h | h
  · refine integrableOn_Ioi_deriv_of_nonneg' hd (fun r _ => ?_)
      (tendsto_log_add_sqrt_sub_div_sub_atTop h₁ h₂)
    exact mul_nonneg (sq_nonneg r) (sub_nonneg.2
      (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)))
  · refine integrableOn_Ioi_deriv_of_nonpos' hd (fun r _ => ?_)
      (tendsto_log_add_sqrt_sub_div_sub_atTop h₁ h₂)
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) (sub_nonpos.2
      (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)))

/-- `∫₀^∞ r² [(r² + D₁)^{-3/2} - (r² + D₂)^{-3/2}] dr = log(D₂/D₁)/2`. -/
theorem integral_Ioi_sq_mul_rpow_neg_three_halves_sub {D₁ D₂ : ℝ} (h₁ : 0 < D₁)
    (h₂ : 0 < D₂) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * ((r ^ 2 + D₁) ^ (-(3 / 2 : ℝ)) - (r ^ 2 + D₂) ^ (-(3 / 2 : ℝ)))
      = Real.log (D₂ / D₁) / 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r (hr : 0 ≤ r) => hasDerivAt_log_add_sqrt_sub_div_sub h₁ h₂ hr)
    (integrableOn_Ioi_sq_mul_rpow_neg_three_halves_sub h₁ h₂)
    (tendsto_log_add_sqrt_sub_div_sub_atTop h₁ h₂)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, zero_div,
    sub_zero]
  rw [Real.log_sqrt h₁.le, Real.log_sqrt h₂.le, Real.log_div h₂.ne' h₁.ne']
  ring

/-! ### Closed forms on `ℝ³` -/

/-- `(|v|² + D)^{-s}` is integrable on `ℝ³` for `D > 0` and `s > 3/2`. -/
theorem integrable_sum_sq_add_rpow {D s : ℝ} (hD : 0 < D) (hs : 3 / 2 < s) :
    Integrable fun v : Fin 3 → ℝ => (∑ k, v k ^ 2 + D) ^ (-s) := by
  obtain ⟨c, hc, hle⟩ := exists_mul_one_add_norm_sq_le (n := 3) 0 hD
  have hint : Integrable (fun v : Fin 3 → ℝ => (1 + ‖v‖) ^ (-(2 * s))) :=
    integrable_one_add_norm (by simp; linarith)
  refine (hint.const_mul (c ^ (-s))).mono' (by fun_prop : Measurable _).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have h1 := hle v 0 D (by simp) le_rfl
  simp only [Pi.zero_apply, add_zero] at h1
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (∑ k, v k ^ 2 + D) ^ (-s) ≤ (c * (1 + ‖v‖) ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    _ = c ^ (-s) * (1 + ‖v‖) ^ (-(2 * s)) := by
        rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        ring_nf

/-- `∫_{ℝ³} (|v|² + D)^{-5/2} d³v = 4π/(3D)`. -/
theorem integral_sum_sq_add_rpow_neg_five_halves {D : ℝ} (hD : 0 < D) :
    ∫ v : Fin 3 → ℝ, (∑ k, v k ^ 2 + D) ^ (-(5 / 2 : ℝ)) = 4 * π / (3 * D) := by
  have h := integral_comp_sum_sq (fun x : ℝ => (x + D) ^ (-(5 / 2 : ℝ)))
  simp only [smul_eq_mul] at h
  rw [h, integral_Ioi_sq_mul_rpow_neg_five_halves hD]
  field_simp

/-- The Pauli–Villars-paired integrand `(|v|² + D₁)^{-3/2} - (|v|² + D₂)^{-3/2}` is
integrable on `ℝ³`. -/
theorem integrable_sum_sq_add_rpow_neg_three_halves_sub {D₁ D₂ : ℝ} (h₁ : 0 < D₁)
    (h₂ : 0 < D₂) :
    Integrable fun v : Fin 3 → ℝ =>
      (∑ k, v k ^ 2 + D₁) ^ (-(3 / 2 : ℝ)) - (∑ k, v k ^ 2 + D₂) ^ (-(3 / 2 : ℝ)) :=
  (integrable_comp_sum_sq_iff
    (fun x : ℝ => (x + D₁) ^ (-(3 / 2 : ℝ)) - (x + D₂) ^ (-(3 / 2 : ℝ)))).2
    (integrableOn_Ioi_sq_mul_rpow_neg_three_halves_sub h₁ h₂)

/-- Pauli–Villars-paired logarithmic integral:
`∫_{ℝ³} [(|v|² + D₁)^{-3/2} - (|v|² + D₂)^{-3/2}] d³v = 2π log(D₂/D₁)`. -/
theorem integral_sum_sq_add_rpow_neg_three_halves_sub {D₁ D₂ : ℝ} (h₁ : 0 < D₁)
    (h₂ : 0 < D₂) :
    ∫ v : Fin 3 → ℝ, ((∑ k, v k ^ 2 + D₁) ^ (-(3 / 2 : ℝ))
      - (∑ k, v k ^ 2 + D₂) ^ (-(3 / 2 : ℝ))) = 2 * π * Real.log (D₂ / D₁) := by
  have h := integral_comp_sum_sq
    (fun x : ℝ => (x + D₁) ^ (-(3 / 2 : ℝ)) - (x + D₂) ^ (-(3 / 2 : ℝ)))
  simp only [smul_eq_mul] at h
  rw [h, integral_Ioi_sq_mul_rpow_neg_three_halves_sub h₁ h₂]
  ring

/-! ### Symmetries of radial integrands -/

/-- In a real normed space, `-x = x` forces `x = 0`. -/
theorem eq_zero_of_neg_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    (h : -x = x) : x = 0 := by
  have h2 : (2 : ℝ) • x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel x
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Odd moments of radial functions vanish (no integrability needed). -/
theorem integral_coord_smul_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (k : Fin 3) :
    ∫ v : Fin 3 → ℝ, v k • g (∑ j, v j ^ 2) = 0 := by
  have h := integral_neg_eq_self (fun v : Fin 3 → ℝ => v k • g (∑ j, v j ^ 2)) volume
  simp only [Pi.neg_apply, neg_sq, neg_smul, integral_neg] at h
  exact eq_zero_of_neg_eq h

/-- Mixed second moments of radial functions vanish (no integrability needed). -/
theorem integral_coord_mul_coord_smul_radial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) {k l : Fin 3} (hkl : k ≠ l) :
    ∫ v : Fin 3 → ℝ, (v k * v l) • g (∑ j, v j ^ 2) = 0 := by
  -- the reflection of the `k`-th coordinate
  let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.piCongrRight fun i =>
    if i = k then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ
  have he : ∀ v i, e v i = if i = k then -v i else v i := by
    intro v i
    change (if i = k then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ) (v i) = _
    split_ifs <;> rfl
  have hmp : MeasurePreserving e volume volume := by
    refine volume_preserving_pi fun i => ?_
    by_cases hi : i = k
    · simp only [hi, ↓reduceIte]
      exact Measure.measurePreserving_neg volume
    · simp only [hi, ↓reduceIte]
      exact MeasurePreserving.id volume
  have h := hmp.integral_comp' (fun v : Fin 3 → ℝ => (v k * v l) • g (∑ j, v j ^ 2))
  have hsq : ∀ v, ∑ j, e v j ^ 2 = ∑ j, v j ^ 2 := by
    intro v
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [he]
    split_ifs <;> simp
  have hk : ∀ v, e v k = -v k := fun v => by rw [he, ite_eq_left rfl]
  have hl : ∀ v, e v l = v l := fun v => by rw [he, ite_eq_right hkl.symm]
  simp only [hsq, hk, hl, neg_mul, neg_smul, integral_neg] at h
  exact eq_zero_of_neg_eq h

/-- A nonzero vector has a nonzero Euclidean square. -/
theorem sum_sq_ne_zero_of_ne_zero {v : Fin 3 → ℝ} (hv : v ≠ 0) : ∑ j, v j ^ 2 ≠ 0 := by
  intro h
  refine hv (funext fun j => ?_)
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).1 h j
    (Finset.mem_univ j)
  simpa using this

/-- Each second moment `v_k² g(|v|²)` is integrable when `|v|² g(|v|²)` is. -/
theorem integrable_coord_sq_smul_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hg : Integrable fun v : Fin 3 → ℝ => (∑ j, v j ^ 2) • g (∑ j, v j ^ 2))
    (k : Fin 3) :
    Integrable fun v : Fin 3 → ℝ => v k ^ 2 • g (∑ j, v j ^ 2) := by
  have h1 : AEStronglyMeasurable (fun v : Fin 3 → ℝ =>
      (v k ^ 2 / ∑ j, v j ^ 2) • ((∑ j, v j ^ 2) • g (∑ j, v j ^ 2))) volume :=
    (by fun_prop : Measurable fun v : Fin 3 → ℝ => v k ^ 2 / ∑ j, v j ^ 2).aestronglyMeasurable.smul
      hg.aestronglyMeasurable
  have h0 : ∀ᵐ v : Fin 3 → ℝ, v ≠ 0 := by
    rw [ae_iff]
    simp
  have hmeas : AEStronglyMeasurable (fun v : Fin 3 → ℝ => v k ^ 2 • g (∑ j, v j ^ 2)) volume := by
    refine h1.congr ?_
    filter_upwards [h0] with v hv
    rw [smul_smul, div_mul_cancel₀ _ (sum_sq_ne_zero_of_ne_zero hv)]
  refine hg.norm.mono' hmeas (Eventually.of_forall fun v => ?_)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg (v j))]
  gcongr
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k)

/-- The second moments `∫ v_k² g(|v|²)` do not depend on `k` (no integrability needed). -/
theorem integral_coord_sq_smul_radial_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (k l : Fin 3) :
    ∫ v : Fin 3 → ℝ, v k ^ 2 • g (∑ j, v j ^ 2) = ∫ v : Fin 3 → ℝ, v l ^ 2 • g (∑ j, v j ^ 2) := by
  -- the transposition of the `k`-th and `l`-th coordinates
  let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
    MeasurableEquiv.arrowCongr' (Equiv.swap k l) (MeasurableEquiv.refl ℝ)
  have he : ∀ v j, e v j = v (Equiv.swap k l j) := fun v j => rfl
  have hmp : MeasurePreserving e :=
    volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)
  have h := hmp.integral_comp' (fun v : Fin 3 → ℝ => v k ^ 2 • g (∑ j, v j ^ 2))
  have hsum : ∀ v : Fin 3 → ℝ, ∑ j, v (Equiv.swap k l j) ^ 2 = ∑ j, v j ^ 2 := fun v =>
    Equiv.sum_comp (Equiv.swap k l) (fun j => v j ^ 2)
  simp only [he, Equiv.swap_apply_left, hsum] at h
  exact h.symm

/-- Isotropy of second moments. -/
theorem integral_coord_sq_smul_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hg : Integrable fun v : Fin 3 → ℝ => (∑ j, v j ^ 2) • g (∑ j, v j ^ 2))
    (k : Fin 3) :
    ∫ v : Fin 3 → ℝ, v k ^ 2 • g (∑ j, v j ^ 2)
      = (1 / 3 : ℝ) • ∫ v : Fin 3 → ℝ, (∑ j, v j ^ 2) • g (∑ j, v j ^ 2) := by
  have hsum : ∫ v : Fin 3 → ℝ, (∑ j, v j ^ 2) • g (∑ j, v j ^ 2)
      = ∑ i, ∫ v : Fin 3 → ℝ, v i ^ 2 • g (∑ j, v j ^ 2) := by
    simp_rw [Finset.sum_smul]
    exact integral_finsetSum _ fun i _ => integrable_coord_sq_smul_radial g hg i
  rw [hsum, Finset.sum_congr rfl fun i _ => integral_coord_sq_smul_radial_eq g i k,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

end QED.Integration

end
