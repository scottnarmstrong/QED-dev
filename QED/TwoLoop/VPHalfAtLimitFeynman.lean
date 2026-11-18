/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.FeynmanParameter
public import QED.Integration.ShiftedEnergyIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Feynman parameters and energy integrals with a power of the photon denominator

Tools for the `ε → 0⁺` limit of the vacuum-polarization class in closed form
(`QED.TwoLoop.VPHalfAt.contractionValue₂_VP_eq_closedForm`, obligation O2-8 at the `ε → 0` level).
After the inner loop is done and its Feynman parameter `x` is integrated by parts, the photon
factor of the outer one-loop vertex is a product of several photon denominators with different
masses and **different prescriptions** (`ε` on the model's photon lines, `ε/(x(1-x))` on the
line of spectral mass `M_f²/(x(1-x))`). Combining all photon denominators by Feynman parameters
gives a single photon denominator `C` raised to a power `n + 1 ≥ 2`, whose mass and prescription
depend on the parameters. This file provides the two one-variable identities behind the
corresponding one-loop vertex with photon factor `C^{-(n+1)}`:

* `inv_sq_mul_pow_eq_integral_feynman`: `1/(X² C^{n+1}) = (n+1)(n+2) ∫₀¹ y (1-y)^n
  (yX + (1-y)C)^{-(n+3)} dy`, by the fundamental theorem of calculus with the primitive
  `(n+1)(n+2) X⁻² (-g^{n+1}/(n+1) + C g^{n+2}/(n+2))`, `g = (1-y)/(yX + (1-y)C)`;
* `inv_mul_mul_pow_eq_integral_feynmanMeasure`: `1/(A B C^{n+1})` as an integral over the unit
  square against `feynmanMeasure`, for `A, B, C` in the open lower half plane;
* `integral_quadratic_mul_shifted_pow`: `∫ (α t² + β t + γ) ((t + a)² + z)^{-(n+2)} dt
  = α (K_{n+1} - K_{n+2}) z^{3/2-(n+2)} + (α a² - β a + γ) K_{n+2} z^{1/2-(n+2)}` for `z` in the
  slit plane, with `K_N = ∫ (1 + s²)^{-N} ds` (`energyConst`). The value of `K_N` is never needed:
  the limits are identified later by comparison with the frozen one-loop vertex.
-/

@[expose] public section

open Complex MeasureTheory Filter Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtLimit

open QED.Integration

/-! ### Feynman parameters with a power of the third denominator -/

/-- **One variable**: `1/(X² C^{n+1}) = (n+1)(n+2) ∫₀¹ y (1-y)^n (yX + (1-y)C)^{-(n+3)} dy`. -/
theorem inv_sq_mul_pow_eq_integral_feynman {X C : ℂ} (hX : X ≠ 0) (hC : C ≠ 0) (n : ℕ)
    (h : ∀ y ∈ Icc (0 : ℝ) 1, (y : ℂ) * X + (1 - y) * C ≠ 0) :
    (X ^ 2 * C ^ (n + 1))⁻¹ = ∫ y in (0 : ℝ)..1,
      ((n + 1) * (n + 2) : ℂ) * ((y : ℂ) * (1 - y) ^ n) *
        ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 3 : ℕ) : ℤ)) := by
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  set G : ℂ → ℂ := fun w => ((n + 1) * (n + 2) : ℂ) * (X ^ 2)⁻¹ *
    (-((1 - w) / (w * X + (1 - w) * C)) ^ (n + 1) / (n + 1) +
      C * ((1 - w) / (w * X + (1 - w) * C)) ^ (n + 2) / (n + 2)) with hG
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => G y)
      (((n + 1) * (n + 2) : ℂ) * ((y : ℂ) * (1 - y) ^ n) *
        ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 3 : ℕ) : ℤ))) y := by
    intro y hy
    have hL := h y (hI ▸ hy)
    have hLd : HasDerivAt (fun w : ℂ => w * X + (1 - w) * C) (X - C) y := by
      have := ((hasDerivAt_id' (x := (y : ℂ))).mul_const X).fun_add
        (((hasDerivAt_id' (x := (y : ℂ))).const_sub 1).mul_const C)
      convert this using 1; ring
    have hg := ((hasDerivAt_id' (x := (y : ℂ))).const_sub 1).fun_div hLd hL
    have hG' := ((((hg.fun_pow (n + 1)).fun_neg).div_const ((n : ℂ) + 1)).fun_add
      (((hg.fun_pow (n + 2)).const_mul C).div_const ((n : ℂ) + 2))).const_mul
      (((n + 1) * (n + 2) : ℂ) * (X ^ 2)⁻¹)
    refine HasDerivAt.comp_ofReal (e := G) ?_
    convert hG' using 1
    rw [zpow_neg, zpow_natCast]
    push_cast
    simp only [div_pow]
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => ((n + 1) * (n + 2) : ℂ) * ((y : ℂ) * (1 - y) ^ n) *
      ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 3 : ℕ) : ℤ))) (uIcc 0 1) :=
    ContinuousOn.mul (by fun_prop)
      (ContinuousOn.zpow₀ (by fun_prop) _ fun y hy => Or.inl (h y (hI ▸ hy)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hG, ofReal_one, ofReal_zero, sub_self, zero_div, ne_eq, add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, zero_pow, neg_zero, zero_add,
    sub_zero, zero_mul, one_mul]
  simp only [inv_pow, one_div]
  field_simp
  ring

/-- A point of the closed unit square gives a combined denominator in the open lower half
plane. -/
theorem im_feynman_combo_neg {A B C : ℂ} (hA : A.im < 0) (hB : B.im < 0) (hC : C.im < 0)
    {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B) + (1 - z.2) * C).im < 0 :=
  im_convex_combo_neg (im_convex_combo_neg hA hB hz.1) hC hz.2

/-- The power Feynman integrand is integrable against `feynmanMeasure`. -/
theorem integrable_feynmanMeasure_pow {A B C : ℂ} (hA : A.im < 0) (hB : B.im < 0)
    (hC : C.im < 0) (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => ((n + 1) * (n + 2) : ℂ) * ((z.2 : ℂ) * (1 - z.2) ^ n) *
      ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B) + (1 - z.2) * C) ^ (-((n + 3 : ℕ) : ℤ)))
      feynmanMeasure := by
  have hcont : ContinuousOn (fun z : ℝ × ℝ => ((n + 1) * (n + 2) : ℂ) *
      ((z.2 : ℂ) * (1 - z.2) ^ n) *
      ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B) + (1 - z.2) * C) ^ (-((n + 3 : ℕ) : ℤ)))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.zpow₀ (by fun_prop) _ fun z hz =>
      Or.inl (ne_zero_of_im_neg (im_feynman_combo_neg hA hB hC hz)))
  rw [feynmanMeasure_eq]
  exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Three denominators, the third to the power `n + 1`, as an iterated interval integral. -/
theorem inv_mul_mul_pow_eq_integral_feynman_three {A B C : ℂ} (hA : A.im < 0) (hB : B.im < 0)
    (hC : C.im < 0) (n : ℕ) :
    (A * B * C ^ (n + 1))⁻¹ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      ((n + 1) * (n + 2) : ℂ) * ((y : ℂ) * (1 - y) ^ n) *
        ((y : ℂ) * ((x : ℂ) * A + (1 - x) * B) + (1 - y) * C) ^ (-((n + 3 : ℕ) : ℤ)) := by
  rw [mul_inv, inv_mul_eq_integral_feynman_two (ne_zero_of_im_neg hB)
    fun x hx => convex_combo_ne_zero hA hB hx, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  have hL := im_convex_combo_neg hA hB hx
  rw [← inv_sq_mul_pow_eq_integral_feynman (ne_zero_of_im_neg hL) (ne_zero_of_im_neg hC) n
    fun y hy => convex_combo_ne_zero hL hC hy, zpow_neg, zpow_ofNat, mul_inv]

/-- **Three denominators, the third to the power `n + 1`**, against `feynmanMeasure`:
`1/(A B C^{n+1}) = ∫ (n+1)(n+2) y (1-y)^n (y(xA + (1-x)B) + (1-y)C)^{-(n+3)} dx dy`. -/
theorem inv_mul_mul_pow_eq_integral_feynmanMeasure {A B C : ℂ} (hA : A.im < 0)
    (hB : B.im < 0) (hC : C.im < 0) (n : ℕ) :
    (A * B * C ^ (n + 1))⁻¹ = ∫ z, ((n + 1) * (n + 2) : ℂ) * ((z.2 : ℂ) * (1 - z.2) ^ n) *
      ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B) + (1 - z.2) * C) ^ (-((n + 3 : ℕ) : ℤ))
        ∂feynmanMeasure := by
  have hint := integrable_feynmanMeasure_pow hA hB hC n
  rw [feynmanMeasure] at hint ⊢
  rw [integral_prod _ hint, inv_mul_mul_pow_eq_integral_feynman_three hA hB hC n]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]

/-! ### The energy integral of a quadratic numerator against a power -/

/-- `K_N = ∫ (1 + s²)^{-N} ds`. -/
noncomputable def energyConst (N : ℕ) : ℝ := ∫ s : ℝ, ((1 + s ^ 2) ^ N)⁻¹

/-- `∫ (t² + z)^{-N} dt = K_N z^{1/2 - N}` on the slit plane, `N ≥ 1`. -/
theorem integral_sq_add_zpow_eq (N : ℕ) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t : ℝ, ((t : ℂ) ^ 2 + z) ^ (-(N : ℤ)) = (energyConst N : ℂ) * z ^ ((1 / 2 : ℂ) - N) :=
  integral_sq_add_zpow_of_real N hN _ (fun _ ha => integral_sq_add_zpow_ofReal N ha rfl) hz

theorem sq_add_ne_zero_of_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) (t : ℝ) :
    (t : ℂ) ^ 2 + z ≠ 0 := by
  obtain ⟨δ, hδ, c, hc, hbd⟩ := exists_lower_bound_add_of_mem_slitPlane hz
  exact sq_add_ne_zero_of_lower_bound hc (hbd z (Metric.mem_ball_self hδ)) t

/-- `t² (t² + z)^{-(n+2)} = (t² + z)^{-(n+1)} - z (t² + z)^{-(n+2)}`. -/
theorem sq_mul_sq_add_zpow {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) (t : ℝ) :
    (t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ)) =
      ((t : ℂ) ^ 2 + z) ^ (-((n + 1 : ℕ) : ℤ)) - z * ((t : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ)) := by
  have h := sq_add_ne_zero_of_mem_slitPlane hz t
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  field_simp
  ring

theorem integrable_sq_mul_sq_add_zpow {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    Integrable fun t : ℝ => (t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ)) := by
  refine ((integrable_sq_add_zpow hz (n + 1) (by omega)).sub
    ((integrable_sq_add_zpow hz (n + 2) (by omega)).const_mul z)).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply]
  rw [sq_mul_sq_add_zpow hz n t]

theorem integrable_mul_sq_add_zpow {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    Integrable fun t : ℝ => (t : ℂ) * ((t : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ)) := by
  have h0 := integrable_sq_add_zpow hz (n + 2) (by omega)
  have h2 := integrable_sq_mul_sq_add_zpow hz n
  refine (h0.norm.add h2.norm).mono'
    (continuous_ofReal.aestronglyMeasurable.mul h0.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  simp only [norm_mul, norm_pow, Pi.add_apply]
  have hx : ‖(t : ℂ)‖ ≤ 1 + ‖(t : ℂ)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖(t : ℂ)‖ - 1), norm_nonneg (t : ℂ)]
  calc ‖(t : ℂ)‖ * ‖((t : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ))‖
      ≤ (1 + ‖(t : ℂ)‖ ^ 2) * ‖((t : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ))‖ := by gcongr
    _ = _ := by ring

/-- The odd moment vanishes, with no integrability hypothesis. -/
theorem integral_mul_sq_add_zpow (z : ℂ) (k : ℤ) :
    ∫ t : ℝ, (t : ℂ) * ((t : ℂ) ^ 2 + z) ^ k = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => (t : ℂ) * ((t : ℂ) ^ 2 + z) ^ k) volume
  simp only [ofReal_neg, neg_sq, neg_mul, integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- `∫ t² (t² + z)^{-(n+2)} dt = (K_{n+1} - K_{n+2}) z^{3/2 - (n+2)}` on the slit plane. -/
theorem integral_sq_mul_sq_add_zpow {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    ∫ t : ℝ, (t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ)) =
      ((energyConst (n + 1) - energyConst (n + 2) : ℝ) : ℂ) *
        z ^ ((3 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ)) := by
  simp_rw [sq_mul_sq_add_zpow hz n]
  rw [integral_sub (integrable_sq_add_zpow hz (n + 1) (by omega))
    ((integrable_sq_add_zpow hz (n + 2) (by omega)).const_mul z), integral_const_mul,
    integral_sq_add_zpow_eq (n + 1) (by omega) hz, integral_sq_add_zpow_eq (n + 2) (by omega) hz]
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have e1 : z ^ ((1 / 2 : ℂ) - ((n + 1 : ℕ) : ℂ)) = z ^ ((3 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ)) := by
    congr 1; push_cast; ring
  have e2 : z * z ^ ((1 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ)) = z ^ ((3 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ)) := by
    rw [show (3 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ) = 1 + ((1 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ)) by ring,
      Complex.cpow_add _ _ hz0, Complex.cpow_one]
  rw [e1, ← mul_assoc, mul_comm z, mul_assoc, e2]
  push_cast
  ring

/-- The quadratic numerator against the shifted power is integrable. -/
theorem integrable_quadratic_mul_shifted_pow {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) (a : ℝ)
    (α β γ : ℂ) :
    Integrable fun t : ℝ =>
      (α * (t : ℂ) ^ 2 + β * t + γ) * (((t : ℂ) + a) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ)) := by
  have i0 := integrable_sq_add_zpow hz (n + 2) (by omega)
  have i1 := integrable_mul_sq_add_zpow hz n
  have i2 := integrable_sq_mul_sq_add_zpow hz n
  refine ((((i2.const_mul α).add (i1.const_mul (β - 2 * a * α))).add
    (i0.const_mul (α * a ^ 2 - β * a + γ))).comp_add_right a).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, ofReal_add]
  ring

/-- **The energy integral of a quadratic numerator against a shifted power.** For `z` in the
slit plane and `n : ℕ`,
`∫ (α t² + β t + γ) ((t + a)² + z)^{-(n+2)} dt
  = α (K_{n+1} - K_{n+2}) z^{3/2-(n+2)} + (α a² - β a + γ) K_{n+2} z^{1/2-(n+2)}`. -/
theorem integral_quadratic_mul_shifted_pow {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) (a : ℝ)
    (α β γ : ℂ) :
    ∫ t : ℝ, (α * (t : ℂ) ^ 2 + β * t + γ) * (((t : ℂ) + a) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ)) =
      α * ((energyConst (n + 1) - energyConst (n + 2) : ℝ) : ℂ) *
          z ^ ((3 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ)) +
        (α * (a : ℂ) ^ 2 - β * a + γ) * (energyConst (n + 2) : ℂ) *
          z ^ ((1 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ)) := by
  have i0 := integrable_sq_add_zpow hz (n + 2) (by omega)
  have i1 := integrable_mul_sq_add_zpow hz n
  have i2 := integrable_sq_mul_sq_add_zpow hz n
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ,
      G = (fun s : ℝ => α * ((s : ℂ) ^ 2 * ((s : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ))))
        + (fun s : ℝ => (β - 2 * a * α) * ((s : ℂ) * ((s : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ))))
        + (fun s : ℝ => (α * a ^ 2 - β * a + γ) * ((s : ℂ) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ))) :=
    ⟨_, rfl⟩
  have hpt : ∀ t : ℝ, (α * (t : ℂ) ^ 2 + β * t + γ) *
      (((t : ℂ) + a) ^ 2 + z) ^ (-((n + 2 : ℕ) : ℤ)) = G (t + a) := fun t => by
    simp only [hG, Pi.add_apply, ofReal_add]
    ring
  simp_rw [hpt]
  rw [integral_add_right_eq_self G a, hG, integral_add' ((i2.const_mul _).add (i1.const_mul _))
    (i0.const_mul _), integral_add' (i2.const_mul _) (i1.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_sq_mul_sq_add_zpow hz n,
    integral_mul_sq_add_zpow, integral_sq_add_zpow_eq (n + 2) (by omega) hz]
  ring

end QED.TwoLoop.VPHalfAtLimit

end
