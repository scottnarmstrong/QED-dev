/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13Def
public import QED.ThreeLoopD.SetDMastersI9Analytic
public import QED.DimReg.CubeMellin
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Set (d), master `I₁₃`: the bubble `b_ε(t)` as a weighted integral over `w = 4x(1 - x)`

The substitution `w = 4x(1 - x)` on each half of `(0, 1)` gives

  `b_ε(t) = ∫₀¹ (1 + t w / 4) ^ (-ε) φ(w) dw`,  `φ(w) = (1 - w) ^ (-1/2) / 2`

(`QED.ThreeLoopD.i13Bub_eq_w`). We record the Taylor polynomial `P(w) = 1/2 + w/4 + 3w²/16` of
`φ` at `0` and the remainder `ψ = (φ - P)/w³`, with `0 ≤ ψ ≤ φ` on `(0, 1)`, and the basic facts
on `b`: the bound `‖b_ε(t)‖ ≤ (1 + t/4) ^ ‖ε‖`, measurability in `t` and holomorphy in `ε`.

## Main results

* `QED.ThreeLoopD.i13Bub_eq_w`, `QED.ThreeLoopD.i13Psi_nonneg`, `QED.ThreeLoopD.i13Psi_le`.
* `QED.ThreeLoopD.norm_i13Bub_le`, `QED.ThreeLoopD.measurable_i13Bub`,
  `QED.ThreeLoopD.differentiable_i13Bub`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-- The weight `φ(w) = (1 - w) ^ (-1/2) / 2`. -/
noncomputable def i13Phi (w : ℝ) : ℝ := (1 - w) ^ (-(1 / 2) : ℝ) / 2

/-- The Taylor polynomial `P(w) = 1/2 + w/4 + 3w²/16` of `φ` at `0`. -/
noncomputable def i13PhiP (w : ℝ) : ℝ := 1 / 2 + w / 4 + 3 / 16 * w ^ 2

/-- The remainder `ψ(w) = (φ(w) - P(w)) / w³`. -/
noncomputable def i13Psi (w : ℝ) : ℝ := (i13Phi w - i13PhiP w) / w ^ 3

theorem i13Phi_eq {w : ℝ} (hw : w < 1) : i13Phi w = 1 / (2 * √(1 - w)) := by
  unfold i13Phi
  rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
  field_simp

theorem i13Phi_pos {w : ℝ} (hw : w < 1) : 0 < i13Phi w := by
  rw [i13Phi_eq hw]
  have : 0 < √(1 - w) := Real.sqrt_pos.mpr (by linarith)
  positivity

@[fun_prop]
theorem measurable_i13Phi : Measurable i13Phi := by
  unfold i13Phi; fun_prop

@[fun_prop]
theorem measurable_i13Psi : Measurable i13Psi := by
  unfold i13Psi i13PhiP; fun_prop

theorem i13Psi_bounds {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 ≤ i13Psi w ∧ i13Psi w ≤ i13Phi w := by
  obtain ⟨h0, h1⟩ := hw
  set s := √(1 - w) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs1 : s < 1 := by
    rw [hs, Real.sqrt_lt' one_pos]; linarith
  have hss : s ^ 2 = 1 - w := Real.sq_sqrt (by linarith)
  have hw' : w = 1 - s ^ 2 := by linarith
  have hphi : i13Phi w = 1 / (2 * s) := i13Phi_eq h1
  have hw3 : 0 < w ^ 3 := pow_pos h0 3
  unfold i13Psi i13PhiP
  rw [hphi]
  have hP : 1 / 2 + w / 4 + 3 / 16 * w ^ 2 = 1 / (2 * s) - (1 - s) ^ 3 * (3 * s ^ 2 + 9 * s + 8)
      / (16 * s) := by
    rw [hw']; field_simp; ring
  have hc0 : 0 ≤ (1 - s) ^ 3 * (3 * s ^ 2 + 9 * s + 8) / (16 * s) := by
    have : 0 < 1 - s := by linarith
    positivity
  constructor
  · apply div_nonneg _ hw3.le
    rw [hP]; linarith
  · rw [div_le_iff₀ hw3, hP]
    have hup : (1 - s) ^ 3 * (3 * s ^ 2 + 9 * s + 8) / (16 * s) ≤ 1 / (2 * s) * w ^ 3 := by
      rw [hw', div_le_iff₀ (by positivity)]
      have : 1 / (2 * s) * (1 - s ^ 2) ^ 3 * (16 * s) = 8 * (1 - s ^ 2) ^ 3 := by
        field_simp; ring
      rw [this]
      have h1 : 0 < 1 - s := by linarith
      nlinarith [mul_pos hs0 (pow_pos h1 3), mul_pos (mul_pos hs0 (pow_pos h1 3)) hs0,
        mul_pos (mul_pos (mul_pos hs0 (pow_pos h1 3)) hs0) hs0]
    linarith

theorem i13Psi_nonneg {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) : 0 ≤ i13Psi w := (i13Psi_bounds hw).1

theorem i13Psi_le {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) : i13Psi w ≤ i13Phi w := (i13Psi_bounds hw).2

/-- `w ^ (r - 1) φ(w) ≤ (w (1 - w)) ^ (r - 1)` on `(0, 1)` for `0 < r ≤ 1/2`. -/
theorem i13_rpow_mul_phi_le {w r : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hr : r ≤ 1 / 2) :
    w ^ (r - 1) * i13Phi w ≤ (w * (1 - w)) ^ (r - 1) := by
  obtain ⟨h0, h1⟩ := hw
  rw [Real.mul_rpow h0.le (by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg h0.le _)
  unfold i13Phi
  have : (1 - w) ^ (-(1 / 2) : ℝ) ≤ (1 - w) ^ (r - 1) :=
    Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by linarith)
  have : 0 ≤ (1 - w) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
  linarith

/-- The majorant `w ^ (r - 1) φ(w)` is integrable for `0 < r ≤ 1/2`. -/
theorem integrableOn_rpow_mul_phi {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) :
    IntegrableOn (fun w : ℝ => w ^ (r - 1) * i13Phi w) (Ioo 0 1) := by
  refine Integrable.mono' (integrableOn_mul_one_sub_rpow_Ioo (a := r - 1) (by linarith))
    (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioo fun w hw => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hw.1.le _)
    (i13Phi_pos hw.2).le)]
  exact i13_rpow_mul_phi_le hw hr

theorem integrableOn_i13Phi : IntegrableOn i13Phi (Ioo 0 1) := by
  refine Integrable.mono' (integrableOn_mul_one_sub_rpow_Ioo (a := -(1 / 2)) (by norm_num))
    (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioo fun w hw => ?_)
  have h := i13_rpow_mul_phi_le hw (r := 1 / 2) le_rfl
  have hw1 : 1 ≤ w ^ ((1 : ℝ) / 2 - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hw.1 hw.2.le (by norm_num)
  have he : (1 : ℝ) / 2 - 1 = -(1 / 2) := by norm_num
  rw [he] at h hw1
  rw [Real.norm_eq_abs, abs_of_pos (i13Phi_pos hw.2)]
  nlinarith [i13Phi_pos hw.2]

/-! ### The substitution `w = 4x(1 - x)` -/

theorem i13_image_quad : (fun x : ℝ => 4 * x * (1 - x)) '' Ioo 0 (1 / 2) = Ioo 0 1 := by
  ext w
  constructor
  · rintro ⟨x, ⟨h0, h1⟩, rfl⟩
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩
    refine ⟨(1 - √(1 - w)) / 2, ⟨?_, ?_⟩, ?_⟩
    · have : √(1 - w) < 1 := by rw [Real.sqrt_lt' one_pos]; linarith
      linarith
    · have : 0 < √(1 - w) := Real.sqrt_pos.mpr (by linarith)
      linarith
    · have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - w by linarith)
      nlinarith

/-- **The substitution** `∫₀¹ g(x(1 - x)) dx = ∫₀¹ g(w/4) φ(w) dw`. -/
theorem i13_integral_quad (g : ℝ → ℂ)
    (hg : IntegrableOn (fun x : ℝ => g (x * (1 - x))) (Ioo 0 1)) :
    ∫ x in Ioo (0 : ℝ) 1, g (x * (1 - x)) = ∫ w in Ioo (0 : ℝ) 1, g (w / 4) * (i13Phi w : ℂ) := by
  -- the two halves
  have hii : IntervalIntegrable (fun x : ℝ => g (x * (1 - x))) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hg
  have hhalf : ∫ x in Ioo (0 : ℝ) 1, g (x * (1 - x)) =
      2 * ∫ x in Ioo (0 : ℝ) (1 / 2), g (x * (1 - x)) := by
    have hA : IntervalIntegrable (fun x : ℝ => g (x * (1 - x))) volume 0 (1 / 2) :=
      hii.mono_set (by
        rw [uIcc_of_le (by norm_num), uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl (by norm_num))
    have hB : IntervalIntegrable (fun x : ℝ => g (x * (1 - x))) volume (1 / 2) 1 :=
      hii.mono_set (by
        rw [uIcc_of_le (by norm_num), uIcc_of_le zero_le_one]
        exact Icc_subset_Icc (by norm_num) le_rfl)
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← intervalIntegral.integral_add_adjacent_intervals hA hB]
    have hsym : ∫ x in (1 / 2 : ℝ)..1, g (x * (1 - x)) =
        ∫ x in (0 : ℝ)..(1 / 2), g (x * (1 - x)) := by
      have := intervalIntegral.integral_comp_sub_left (a := (1 / 2 : ℝ)) (b := 1)
        (fun x : ℝ => g (x * (1 - x))) 1
      norm_num at this
      rw [← this]
      congr 1
      ext x
      ring_nf
    rw [hsym]
    ring
  -- the substitution on `(0, 1/2)`
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => 4 * x * (1 - x))
    (f' := fun x => 4 - 8 * x) (s := Ioo 0 (1 / 2)) measurableSet_Ioo
    (fun x _ => by
      have := ((hasDerivAt_id x).const_mul 4).mul ((hasDerivAt_id x).const_sub 1)
      exact (this.congr_deriv (by simp; ring)).hasDerivWithinAt)
    (fun x hx y hy hxy => by
      simp only at hxy
      have : (x - y) * (4 - 4 * (x + y)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exfalso; linarith [hx.2, hy.2])
    (fun w => g (w / 4) * (i13Phi w : ℂ))
  rw [i13_image_quad] at hcov
  rw [hcov, hhalf, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  obtain ⟨h0, h1⟩ := hx
  have hq : 1 - 4 * x * (1 - x) = (1 - 2 * x) ^ 2 := by ring
  have hphi : i13Phi (4 * x * (1 - x)) = 1 / (2 * (1 - 2 * x)) := by
    rw [i13Phi_eq (by nlinarith), hq, Real.sqrt_sq (by linarith)]
  rw [hphi, abs_of_pos (by linarith), real_smul,
    show 4 * x * (1 - x) / 4 = x * (1 - x) by ring]
  have hne : ((1 - 2 * x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  push_cast at hne ⊢
  field_simp
  ring

/-! ### The bubble -/

theorem i13_base_pos {x t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) :
    0 < 1 + x * (1 - x) * t := by
  have : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
  positivity

theorem continuousOn_i13Bub_integrand (ε : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun x : ℝ => ((1 + x * (1 - x) * t : ℝ) : ℂ) ^ (-ε)) (Icc 0 1) := by
  refine ContinuousOn.cpow_const (by fun_prop) fun x hx => ?_
  exact ofReal_mem_slitPlane.mpr (i13_base_pos hx ht)

theorem integrableOn_i13Bub_integrand (ε : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun x : ℝ => ((1 + x * (1 - x) * t : ℝ) : ℂ) ^ (-ε)) (Ioo 0 1) :=
  ((continuousOn_i13Bub_integrand ε ht).integrableOn_compact isCompact_Icc).mono_set
    Ioo_subset_Icc_self

/-- **The bubble in the variable `w`**: `b_ε(t) = ∫₀¹ (1 + t w/4) ^ (-ε) φ(w) dw`. -/
theorem i13Bub_eq_w (ε : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    i13Bub ε t = ∫ w in Ioo (0 : ℝ) 1, ((1 + t * w / 4 : ℝ) : ℂ) ^ (-ε) * (i13Phi w : ℂ) := by
  have := i13_integral_quad (fun c => ((1 + c * t : ℝ) : ℂ) ^ (-ε))
    (integrableOn_i13Bub_integrand ε ht)
  unfold i13Bub
  convert this using 3 with w
  ring_nf

theorem norm_i13Bub_integrand_le (ε : ℂ) {x t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) :
    ‖((1 + x * (1 - x) * t : ℝ) : ℂ) ^ (-ε)‖ ≤ (1 + t / 4) ^ ‖ε‖ := by
  have hb := i13_base_pos hx ht
  rw [norm_cpow_eq_rpow_re_of_pos hb]
  have hc : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have h1 : 1 ≤ 1 + x * (1 - x) * t := by
    have : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
    nlinarith
  calc (1 + x * (1 - x) * t) ^ (-ε).re ≤ (1 + x * (1 - x) * t) ^ ‖ε‖ :=
        Real.rpow_le_rpow_of_exponent_le h1 (by
          rw [neg_re]; exact (neg_le_abs _).trans (abs_re_le_norm ε))
    _ ≤ (1 + t / 4) ^ ‖ε‖ := Real.rpow_le_rpow (by linarith) (by nlinarith) (norm_nonneg _)

/-- `‖b_ε(t)‖ ≤ (1 + t/4) ^ ‖ε‖` for `t ≥ 0`. -/
theorem norm_i13Bub_le (ε : ℂ) {t : ℝ} (ht : 0 ≤ t) : ‖i13Bub ε t‖ ≤ (1 + t / 4) ^ ‖ε‖ := by
  unfold i13Bub
  have := norm_setIntegral_le_of_norm_le_const (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := volume) (a := (0 : ℝ)) (b := 1))
    (C := (1 + t / 4) ^ ‖ε‖) (f := fun x : ℝ => ((1 + x * (1 - x) * t : ℝ) : ℂ) ^ (-ε))
    (fun x hx => norm_i13Bub_integrand_le ε (Ioo_subset_Icc_self hx) ht)
  simpa [Real.volume_real_Ioo_of_le zero_le_one] using this

theorem measurable_i13Bub (ε : ℂ) : Measurable fun t => i13Bub ε t := by
  unfold i13Bub
  have : StronglyMeasurable (fun p : ℝ × ℝ => ((1 + p.2 * (1 - p.2) * p.1 : ℝ) : ℂ) ^ (-ε)) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ =>
      ((1 + p.2 * (1 - p.2) * p.1 : ℝ) : ℂ) ^ (-ε)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable

/-- `ε ↦ b_ε(t)` is entire for `t ≥ 0`. -/
theorem differentiable_i13Bub {t : ℝ} (ht : 0 ≤ t) : Differentiable ℂ fun ε => i13Bub ε t := by
  intro ε₀
  unfold i13Bub
  refine QED.DimReg.differentiableAt_integral_of_holomorphic one_pos
    (b := fun _ => (1 + t / 4) ^ (‖ε₀‖ + 1)) (integrable_const _)
    (fun ε _ => (integrableOn_i13Bub_integrand ε ht).aestronglyMeasurable) ?_ ?_
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ε hε => ?_
    rw [mem_ball, dist_eq_norm] at hε
    refine (norm_i13Bub_integrand_le ε (Ioo_subset_Icc_self hx) ht).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le (by linarith)
      (by linarith [norm_sub_norm_le ε ε₀])
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_
    have hb := i13_base_pos (Ioo_subset_Icc_self hx) ht
    exact (Differentiable.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr hb.ne'))).differentiableOn

end QED.ThreeLoopD
