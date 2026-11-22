/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9KTaylor
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₉`: the coefficient `K₁ = -10`

With `v = 1 - w`, `P - w = c v²` and `P - c = w (1 - c - c v)`, the integrand of
`K₁ = QED.ThreeLoopD.i9KCoeff 1` splits, on the open square, into five nonpositive pieces:

  `(b₁ P - b₂ w - b₃ c) / (c w) = 3 log (c / P) / w + 3 log (w / P) / c + 3 (2 - w) log P
    - 2 (2 - w) log c - 2 (2 - w) log w`

(`c ≤ P`, `w ≤ P ≤ 1`). Each is integrated by Tonelli, the inner integral by an explicit
antiderivative (`P = (x + (1 - x) w)(1 - x + x w)` splits `log P`):

* `∫∫ log (c / P) / w = ∫ 2 log w / (1 - w) dw = -π²/3` (inner integral over `x`);
* `∫∫ log (w / P) / c = ∫ (1 + x log x / (1 - x) + (1 - x) log (1 - x) / x) / c dx = -2`;
* `∫∫ (2 - w) log P = -2 ∫ (2 - w)(1 + w log w / (1 - w)) dw = -9/2 + π²/3`;
* `∫∫ (2 - w) log c = -3`, `∫∫ (2 - w) log w = -7/4`.

Hence `K₁ = -π² - 6 - 27/2 + π² + 6 + 7/2 = -10`.

## Main results

* `QED.ThreeLoopD.i9KCoeff_one`: `K₁ = -10`.
* `QED.ThreeLoopD.hasTruncLaurent_i9K_of_coeff23`: the expansion of `K` through `ε³`, given
  `K₂` and `K₃`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopD

/-! ### Tools -/

/-- Tonelli on the open square for a nonpositive function, inner integral over `y`. -/
theorem i9_square_nonpos {f : ℝ × ℝ → ℝ} {g : ℝ → ℝ} {V : ℝ} (hm : Measurable f)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, f (x, y) ≤ 0)
    (hin : ∀ x ∈ Ioo (0 : ℝ) 1,
      IntegrableOn (fun y => f (x, y)) (Ioo 0 1) ∧ ∫ y in Ioo (0 : ℝ) 1, f (x, y) = g x)
    (hg : IntegrableOn g (Ioo 0 1)) (hV : ∫ x in Ioo (0 : ℝ) 1, g x = V) :
    IntegrableOn f (Ioo 0 1 ×ˢ Ioo 0 1) ∧ ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, f z = V := by
  have hint : Integrable f ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => (hin x hx).1, ?_⟩
    refine hg.neg.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Pi.neg_apply, ← (hin x hx).2, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    simp [Real.norm_eq_abs, abs_of_nonpos (hf x hx y hy)]
  refine ⟨by rwa [IntegrableOn, volume_restrict_prod2], ?_⟩
  rw [volume_restrict_prod2, integral_prod f hint, ← hV]
  exact setIntegral_congr_fun measurableSet_Ioo fun x hx => (hin x hx).2

/-- Tonelli on the open square for a nonpositive function, inner integral over `x`. -/
theorem i9_square_nonpos' {f : ℝ × ℝ → ℝ} {g : ℝ → ℝ} {V : ℝ} (hm : Measurable f)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, f (x, y) ≤ 0)
    (hin : ∀ y ∈ Ioo (0 : ℝ) 1,
      IntegrableOn (fun x => f (x, y)) (Ioo 0 1) ∧ ∫ x in Ioo (0 : ℝ) 1, f (x, y) = g y)
    (hg : IntegrableOn g (Ioo 0 1)) (hV : ∫ y in Ioo (0 : ℝ) 1, g y = V) :
    IntegrableOn f (Ioo 0 1 ×ˢ Ioo 0 1) ∧ ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, f z = V := by
  have hint : Integrable f ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [integrable_prod_iff' hm.aestronglyMeasurable]
    refine ⟨ae_restrict_of_forall_mem measurableSet_Ioo fun y hy => (hin y hy).1, ?_⟩
    refine hg.neg.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [Pi.neg_apply, ← (hin y hy).2, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp [Real.norm_eq_abs, abs_of_nonpos (hf x hx y hy)]
  refine ⟨by rwa [IntegrableOn, volume_restrict_prod2], ?_⟩
  rw [volume_restrict_prod2, integral_prod_symm f hint, ← hV]
  exact setIntegral_congr_fun measurableSet_Ioo fun y hy => (hin y hy).2

/-- A nonpositive function with an antiderivative having one-sided limits at `0` and `1`. -/
theorem i9_Ioo_of_nonpos {F f : ℝ → ℝ} {A B : ℝ}
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ≤ 0)
    (h0 : Tendsto F (𝓝[>] 0) (𝓝 A)) (h1 : Tendsto F (𝓝[<] 1) (𝓝 B)) :
    IntegrableOn f (Ioo 0 1) ∧ ∫ x in Ioo (0 : ℝ) 1, f x = B - A := by
  obtain ⟨hi, hv⟩ := QED.Polylog.intervalIntegrable_and_integral_eq_of_nonpos hd hf h0 h1
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hi, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hv]

/-- The same, with an antiderivative continuous on `[0, 1]`. -/
theorem i9_Ioo_of_nonpos_cont {F f : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 1))
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ≤ 0) :
    IntegrableOn f (Ioo 0 1) ∧ ∫ x in Ioo (0 : ℝ) 1, f x = F 1 - F 0 := by
  refine i9_Ioo_of_nonpos hd hf ?_ ?_
  · rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
    exact ((hF 0 ⟨le_rfl, zero_le_one⟩).mono Ioo_subset_Icc_self).tendsto
  · rw [← nhdsWithin_Ioo_eq_nhdsLT zero_lt_one]
    exact ((hF 1 ⟨zero_le_one, le_rfl⟩).mono Ioo_subset_Icc_self).tendsto

/-- `t log t` along an affine map. -/
theorem i9_hasDerivAt_mulLog {a b x : ℝ} (h : 0 < a + b * x) :
    HasDerivAt (fun x => (a + b * x) * Real.log (a + b * x))
      (b * (Real.log (a + b * x) + 1)) x := by
  have h1 : HasDerivAt (fun x => a + b * x) b x := by
    simpa using ((hasDerivAt_id x).const_mul b).const_add a
  have := (Real.hasDerivAt_mul_log h.ne').comp x h1
  rw [show b * (Real.log (a + b * x) + 1) = (Real.log (a + b * x) + 1) * b by ring]
  exact this

theorem i9_continuous_mulLog (a b : ℝ) :
    Continuous (fun x : ℝ => (a + b * x) * Real.log (a + b * x)) :=
  Real.continuous_mul_log.comp (by fun_prop)

theorem i9Poly_one_eq (x w : ℝ) : i9Poly x w 1 = (x + (1 - x) * w) * (1 - x + x * w) := by
  unfold i9Poly; ring

theorem log_i9Poly_one {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    Real.log (i9Poly x w 1) = Real.log (w + (1 - w) * x) + Real.log (1 + (-(1 - w)) * x) := by
  have hA : 0 < x + (1 - x) * w := by nlinarith [hx.1, hx.2, hw.1, hw.2]
  have hB : 0 < 1 - x + x * w := by nlinarith [hx.1, hx.2, hw.1, hw.2]
  rw [i9Poly_one_eq, Real.log_mul hA.ne' hB.ne']
  congr 2 <;> ring

theorem i9_c_le_poly {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    x * (1 - x) ≤ i9Poly x w 1 := by
  unfold i9Poly
  nlinarith [i9_c_le x, i9_c_pos hx, hw.1, hw.2, mul_pos (i9_c_pos hx) hw.1]

theorem i9_w_le_poly {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (w : ℝ) :
    w ≤ i9Poly x w 1 := by
  unfold i9Poly
  nlinarith [i9_c_pos hx, sq_nonneg (1 - w)]

theorem i9_poly_le_one {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    i9Poly x w 1 ≤ 1 := by
  rw [i9Poly_one_eq]
  have hA : x + (1 - x) * w ≤ 1 := by nlinarith [hx.1, hx.2, hw.1, hw.2]
  have hB : 1 - x + x * w ≤ 1 := by nlinarith [hx.1, hx.2, hw.1, hw.2]
  have hA0 : 0 ≤ x + (1 - x) * w := by nlinarith [hx.1, hx.2, hw.1, hw.2]
  nlinarith [hx.1, hx.2, hw.1, hw.2]

theorem i9_hasDerivAt_mulLog' {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => x * Real.log x) (Real.log x + 1) x :=
  Real.hasDerivAt_mul_log hx.ne'

/-! ### The pieces `∫∫ (2 - w) log w` and `∫∫ (2 - w) log c` -/

theorem i9K1_piece5 :
    IntegrableOn (fun z : ℝ × ℝ => (2 - z.2) * Real.log z.2) (Ioo 0 1 ×ˢ Ioo 0 1) ∧
      ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, (2 - z.2) * Real.log z.2 = -7 / 4 := by
  have hin : ∀ w ∈ Ioo (0 : ℝ) 1, (2 - w) * Real.log w ≤ 0 := fun w hw =>
    mul_nonpos_of_nonneg_of_nonpos (by linarith [hw.2]) (Real.log_nonpos hw.1.le hw.2.le)
  have h1 := i9_Ioo_of_nonpos_cont (F := fun w => 2 * (w * Real.log w) - 2 * w -
      w * (w * Real.log w) / 2 + w ^ 2 / 4) (f := fun w => (2 - w) * Real.log w)
    (by have := Real.continuous_mul_log; fun_prop)
    (fun w hw => by
      have h := i9_hasDerivAt_mulLog' hw.1
      exact ((((h.const_mul 2).sub ((hasDerivAt_id' w).const_mul 2)).sub
        (((hasDerivAt_id' w).mul h).div_const 2)).add
          ((hasDerivAt_pow 2 w).div_const 4)).congr_deriv (by norm_num; ring)) hin
  norm_num at h1
  refine i9_square_nonpos (g := fun _ => -7 / 4) (by fun_prop)
    (fun x _ w hw => hin w hw) (fun x _ => ⟨h1.1, by rw [h1.2]; norm_num⟩)
    (integrableOn_const (by simp)) (by simp)

theorem i9K1_piece4 :
    IntegrableOn (fun z : ℝ × ℝ => (2 - z.2) * Real.log (z.1 * (1 - z.1)))
        (Ioo 0 1 ×ˢ Ioo 0 1) ∧
      ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, (2 - z.2) * Real.log (z.1 * (1 - z.1)) = -3 := by
  have hL : ∀ x ∈ Ioo (0 : ℝ) 1, Real.log (x * (1 - x)) ≤ 0 := fun x hx =>
    Real.log_nonpos (i9_c_pos hx).le (by nlinarith [i9_c_le x])
  refine i9_square_nonpos (g := fun x => 3 / 2 * Real.log (x * (1 - x)))
    (by fun_prop) (fun x hx w hw => mul_nonpos_of_nonneg_of_nonpos (by linarith [hw.2])
      (hL x hx)) (fun x hx => ?_) ?_ ?_
  · have h := i9_Ioo_of_nonpos_cont (F := fun w => (2 * w - w ^ 2 / 2) * Real.log (x * (1 - x)))
      (f := fun w => (2 - w) * Real.log (x * (1 - x))) (by fun_prop)
      (fun w _ => by
        exact ((((hasDerivAt_id' w).const_mul 2).sub
          ((hasDerivAt_pow 2 w).div_const 2)).mul_const
            (Real.log (x * (1 - x)))).congr_deriv (by norm_num))
      (fun w hw => mul_nonpos_of_nonneg_of_nonpos (by linarith [hw.2]) (hL x hx))
    refine ⟨h.1, ?_⟩
    rw [h.2]
    ring
  · have h := i9_Ioo_of_nonpos_cont (F := fun x => 3 / 2 * (x * Real.log x - x -
        (1 + -1 * x) * Real.log (1 + -1 * x) - x))
      (f := fun x => 3 / 2 * Real.log (x * (1 - x)))
      (by have := Real.continuous_mul_log; have := i9_continuous_mulLog 1 (-1); fun_prop)
      (fun x hx => by
        have h1 := i9_hasDerivAt_mulLog' hx.1
        have h2 := i9_hasDerivAt_mulLog (a := 1) (b := -1) (x := x) (by linarith [hx.2])
        refine ((((h1.sub (hasDerivAt_id' x)).sub h2).sub
          (hasDerivAt_id' x)).const_mul (3 / 2 : ℝ)).congr_deriv ?_
        rw [Real.log_mul hx.1.ne' (by linarith [hx.2])]
        ring_nf)
      (fun x hx => by have := hL x hx; linarith)
    exact h.1
  · have h := i9_Ioo_of_nonpos_cont (F := fun x => 3 / 2 * (x * Real.log x - x -
        (1 + -1 * x) * Real.log (1 + -1 * x) - x))
      (f := fun x => 3 / 2 * Real.log (x * (1 - x)))
      (by have := Real.continuous_mul_log; have := i9_continuous_mulLog 1 (-1); fun_prop)
      (fun x hx => by
        have h1 := i9_hasDerivAt_mulLog' hx.1
        have h2 := i9_hasDerivAt_mulLog (a := 1) (b := -1) (x := x) (by linarith [hx.2])
        refine ((((h1.sub (hasDerivAt_id' x)).sub h2).sub
          (hasDerivAt_id' x)).const_mul (3 / 2 : ℝ)).congr_deriv ?_
        rw [Real.log_mul hx.1.ne' (by linarith [hx.2])]
        ring_nf)
      (fun x hx => by have := hL x hx; linarith)
    rw [h.2]
    norm_num

/-! ### The piece `∫∫ log (c / P) / w` -/

/-- `∫₀¹ log w / (1 - w) dw = -π²/6`. -/
theorem i9_log_div_one_sub :
    IntegrableOn (fun w => Real.log w / (1 - w)) (Ioo 0 1) ∧
      ∫ w in Ioo (0 : ℝ) 1, Real.log w / (1 - w) = -(π ^ 2 / 6) := by
  obtain ⟨hi, hv⟩ := QED.Polylog.intervalIntegrable_and_integral_log_one_sub_div
  have e : (fun w : ℝ => Real.log (1 - (1 - w)) / (1 - w)) = fun w => Real.log w / (1 - w) := by
    funext w; rw [sub_sub_cancel]
  have hi' : IntervalIntegrable (fun w => Real.log w / (1 - w)) volume 0 1 := by
    have := hi.comp_sub_left 1
    rw [e] at this
    simpa using this.symm
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hi', ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, ← e,
    intervalIntegral.integral_comp_sub_left (fun x => Real.log (1 - x) / x) 1]
  simpa using hv

theorem i9K1_piece1 :
    IntegrableOn (fun z : ℝ × ℝ => (Real.log (z.1 * (1 - z.1)) - Real.log (i9Poly z.1 z.2 1)) / z.2)
        (Ioo 0 1 ×ˢ Ioo 0 1) ∧
      ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        (Real.log (z.1 * (1 - z.1)) - Real.log (i9Poly z.1 z.2 1)) / z.2 = -(π ^ 2 / 3) := by
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1,
      (Real.log (x * (1 - x)) - Real.log (i9Poly x w 1)) / w ≤ 0 := fun x hx w hw =>
    div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (Real.log_le_log (i9_c_pos hx) (i9_c_le_poly hx hw))) hw.1.le
  obtain ⟨hgi, hgv⟩ := i9_log_div_one_sub
  refine i9_square_nonpos' (g := fun w => 2 * (Real.log w / (1 - w)))
    (by unfold i9Poly; fun_prop) hf (fun w hw => ?_) (hgi.const_mul 2) (by
      rw [integral_const_mul, hgv]; ring)
  have hd : 0 < 1 - w := by linarith [hw.2]
  have hw0 : w ≠ 0 := hw.1.ne'
  have h := i9_Ioo_of_nonpos_cont (F := fun x => (x * Real.log x - x -
      (1 + -1 * x) * Real.log (1 + -1 * x) - x -
      ((w + (1 - w) * x) * Real.log (w + (1 - w) * x) - (w + (1 - w) * x)) / (1 - w) +
      ((1 + -(1 - w) * x) * Real.log (1 + -(1 - w) * x) - (1 + -(1 - w) * x)) / (1 - w)) / w)
    (f := fun x => (Real.log (x * (1 - x)) - Real.log (i9Poly x w 1)) / w)
    (by
      have := Real.continuous_mul_log; have := i9_continuous_mulLog 1 (-1)
      have := i9_continuous_mulLog w (1 - w); have := i9_continuous_mulLog 1 (-(1 - w))
      fun_prop)
    (fun x hx => by
      have hA : 0 < w + (1 - w) * x := by nlinarith [hx.1, hx.2, hw.1, hw.2]
      have hB : 0 < 1 + -(1 - w) * x := by nlinarith [hx.1, hx.2, hw.1, hw.2]
      have h1 := i9_hasDerivAt_mulLog' hx.1
      have h2 := i9_hasDerivAt_mulLog (a := 1) (b := -1) (x := x) (by linarith [hx.2])
      have h3 := i9_hasDerivAt_mulLog (a := w) (b := 1 - w) (x := x) hA
      have h4 := i9_hasDerivAt_mulLog (a := 1) (b := -(1 - w)) (x := x) hB
      have l3 : HasDerivAt (fun x => w + (1 - w) * x) (1 - w) x := by
        simpa using ((hasDerivAt_id' x).const_mul (1 - w)).const_add w
      have l4 : HasDerivAt (fun x => 1 + -(1 - w) * x) (-(1 - w)) x := by
        simpa using ((hasDerivAt_id' x).const_mul (-(1 - w))).const_add 1
      refine ((((((h1.sub (hasDerivAt_id' x)).sub h2).sub (hasDerivAt_id' x)).sub
        ((h3.sub l3).div_const (1 - w))).add ((h4.sub l4).div_const (1 - w))).div_const
          w).congr_deriv ?_
      rw [Real.log_mul hx.1.ne' (by linarith [hx.2]), log_i9Poly_one hx hw]
      field_simp
      ring_nf)
    (fun x hx => hf x hx w hw)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp
  field_simp
  ring

/-! ### The piece `∫∫ (2 - w) log P` -/

theorem i9_one_sub_mul_log :
    IntegrableOn (fun w => (1 - w) * Real.log w) (Ioo 0 1) ∧
      ∫ w in Ioo (0 : ℝ) 1, (1 - w) * Real.log w = -3 / 4 := by
  have h := i9_Ioo_of_nonpos_cont (F := fun w => w * Real.log w - w -
      w * (w * Real.log w) / 2 + w ^ 2 / 4) (f := fun w => (1 - w) * Real.log w)
    (by have := Real.continuous_mul_log; fun_prop)
    (fun w hw => by
      have h := i9_hasDerivAt_mulLog' hw.1
      exact (((h.sub (hasDerivAt_id' w)).sub (((hasDerivAt_id' w).mul h).div_const 2)).add
          ((hasDerivAt_pow 2 w).div_const 4)).congr_deriv (by norm_num; ring))
    (fun w hw => mul_nonpos_of_nonneg_of_nonpos (by linarith [hw.2])
      (Real.log_nonpos hw.1.le hw.2.le))
  exact ⟨h.1, by rw [h.2]; norm_num⟩

theorem i9_two_sub :
    IntegrableOn (fun w : ℝ => -2 * (2 - w)) (Ioo 0 1) ∧
      ∫ w in Ioo (0 : ℝ) 1, -2 * (2 - w) = -3 := by
  have h := i9_Ioo_of_nonpos_cont (F := fun w => -2 * (2 * w - w ^ 2 / 2))
    (f := fun w : ℝ => -2 * (2 - w)) (by fun_prop)
    (fun w _ => ((((hasDerivAt_id' w).const_mul 2).sub
      ((hasDerivAt_pow 2 w).div_const 2)).const_mul (-2)).congr_deriv (by norm_num))
    (fun w hw => by nlinarith [hw.2])
  exact ⟨h.1, by rw [h.2]; norm_num⟩

theorem i9K1_piece3 :
    IntegrableOn (fun z : ℝ × ℝ => (2 - z.2) * Real.log (i9Poly z.1 z.2 1))
        (Ioo 0 1 ×ˢ Ioo 0 1) ∧
      ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, (2 - z.2) * Real.log (i9Poly z.1 z.2 1) =
        -9 / 2 + π ^ 2 / 3 := by
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1,
      (2 - w) * Real.log (i9Poly x w 1) ≤ 0 := fun x hx w hw =>
    mul_nonpos_of_nonneg_of_nonpos (by linarith [hw.2])
      (Real.log_nonpos (i9Poly_one_pos hx hw).le (i9_poly_le_one hx hw))
  obtain ⟨ha, hav⟩ := i9_two_sub
  obtain ⟨hb, hbv⟩ := i9_log_div_one_sub
  obtain ⟨hc, hcv⟩ := i9_one_sub_mul_log
  have hg : EqOn (fun w => -2 * (2 - w) * (1 + w * Real.log w / (1 - w)))
      (fun w => -2 * (2 - w) - 2 * (Real.log w / (1 - w)) + 2 * ((1 - w) * Real.log w))
      (Ioo 0 1) := fun w hw => by
    have : 1 - w ≠ 0 := by linarith [hw.2]
    field_simp
    ring
  refine i9_square_nonpos' (g := fun w => -2 * (2 - w) * (1 + w * Real.log w / (1 - w)))
    (by unfold i9Poly; fun_prop) hf (fun w hw => ?_) ?_ ?_
  · have hd : 0 < 1 - w := by linarith [hw.2]
    have h := i9_Ioo_of_nonpos_cont (F := fun x => (2 - w) *
        (((w + (1 - w) * x) * Real.log (w + (1 - w) * x) - (w + (1 - w) * x)) / (1 - w) -
        ((1 + -(1 - w) * x) * Real.log (1 + -(1 - w) * x) - (1 + -(1 - w) * x)) / (1 - w)))
      (f := fun x => (2 - w) * Real.log (i9Poly x w 1))
      (by
        have := i9_continuous_mulLog w (1 - w); have := i9_continuous_mulLog 1 (-(1 - w))
        fun_prop)
      (fun x hx => by
        have hA : 0 < w + (1 - w) * x := by nlinarith [hx.1, hx.2, hw.1, hw.2]
        have hB : 0 < 1 + -(1 - w) * x := by nlinarith [hx.1, hx.2, hw.1, hw.2]
        have h3 := i9_hasDerivAt_mulLog (a := w) (b := 1 - w) (x := x) hA
        have h4 := i9_hasDerivAt_mulLog (a := 1) (b := -(1 - w)) (x := x) hB
        have l3 : HasDerivAt (fun x => w + (1 - w) * x) (1 - w) x := by
          simpa using ((hasDerivAt_id' x).const_mul (1 - w)).const_add w
        have l4 : HasDerivAt (fun x => 1 + -(1 - w) * x) (-(1 - w)) x := by
          simpa using ((hasDerivAt_id' x).const_mul (-(1 - w))).const_add 1
        refine ((((h3.sub l3).div_const (1 - w)).sub ((h4.sub l4).div_const
          (1 - w))).const_mul (2 - w)).congr_deriv ?_
        rw [log_i9Poly_one hx hw]
        field_simp
        ring_nf)
      (fun x hx => hf x hx w hw)
    refine ⟨h.1, ?_⟩
    rw [h.2]
    simp
    field_simp
    ring
  · exact ((ha.sub (hb.const_mul 2)).add (hc.const_mul 2)).congr_fun hg.symm measurableSet_Ioo
  · rw [setIntegral_congr_fun measurableSet_Ioo hg, integral_add, integral_sub,
      hav, integral_const_mul, integral_const_mul, hbv, hcv]
    · ring
    exacts [ha, hb.const_mul 2, ha.sub (hb.const_mul 2), hc.const_mul 2]

/-! ### The piece `∫∫ log (w / P) / c` -/

theorem log_i9Poly_one' {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    Real.log (i9Poly x w 1) = Real.log (x + (1 - x) * w) + Real.log ((1 - x) + x * w) := by
  have hA : 0 < x + (1 - x) * w := by nlinarith [hx.1, hx.2, hw.1, hw.2]
  have hB : 0 < 1 - x + x * w := by nlinarith [hx.1, hx.2, hw.1, hw.2]
  rw [i9Poly_one_eq, Real.log_mul hA.ne' hB.ne']

theorem i9_tendsto_log_div_one_sub :
    Tendsto (fun x => Real.log x / (1 - x)) (𝓝[<] 1) (𝓝 (-1)) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_log one_ne_zero)
  have h' : Tendsto (fun x => -slope Real.log 1 x) (𝓝[<] 1) (𝓝 (-1)) := by
    simpa using (h.mono_left (nhdsWithin_mono (s := Iio 1) (t := {1}ᶜ) 1
      fun x hx => ne_of_lt hx)).neg
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
  have h2 : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx).symm
  rw [slope_def_field, Real.log_one]
  field_simp
  ring

/-- The antiderivative of the outer integrand of `∫∫ log (w / P) / c`. -/
noncomputable def i9K1G (x : ℝ) : ℝ :=
  -((1 + -1 * x) * Real.log (1 + -1 * x)) / x + x * Real.log x / (1 - x)

theorem i9K1G_tendsto_zero : Tendsto i9K1G (𝓝[>] 0) (𝓝 1) := by
  have hφ : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => 1 - x) (𝓝 0) (𝓝 (1 - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have hA := i9_tendsto_log_div_one_sub.comp hφ
  have hB : Tendsto (fun x : ℝ => 1 + -1 * x) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun x : ℝ => 1 + -1 * x) (𝓝 0) (𝓝 (1 + -1 * 0)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hC : Tendsto (fun x : ℝ => x * Real.log x / (1 - x)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => x * Real.log x / (1 - x)) 0 :=
      (Real.continuous_mul_log.continuousAt).div (by fun_prop) (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have := ((hB.mul hA).neg).add hC
  norm_num at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp only [i9K1G]
  field_simp
  ring_nf

theorem i9K1G_tendsto_one : Tendsto i9K1G (𝓝[<] 1) (𝓝 (-1)) := by
  have hA : Tendsto (fun x : ℝ => -((1 + -1 * x) * Real.log (1 + -1 * x)) / x) (𝓝[<] 1)
      (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => -((1 + -1 * x) * Real.log (1 + -1 * x)) / x) 1 :=
      ((i9_continuous_mulLog 1 (-1)).continuousAt.neg).div (by fun_prop) (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have := hA.add (hB.mul i9_tendsto_log_div_one_sub)
  norm_num at this
  refine this.congr' (Eventually.of_forall fun x => ?_)
  simp only [i9K1G]
  ring_nf

theorem i9K1_piece2 :
    IntegrableOn (fun z : ℝ × ℝ => (Real.log z.2 - Real.log (i9Poly z.1 z.2 1)) /
        (z.1 * (1 - z.1))) (Ioo 0 1 ×ˢ Ioo 0 1) ∧
      ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        (Real.log z.2 - Real.log (i9Poly z.1 z.2 1)) / (z.1 * (1 - z.1)) = -2 := by
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1,
      (Real.log w - Real.log (i9Poly x w 1)) / (x * (1 - x)) ≤ 0 := fun x hx w hw =>
    div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (Real.log_le_log hw.1 (i9_w_le_poly hx w))) (i9_c_pos hx).le
  set g : ℝ → ℝ := fun x =>
    (1 + x * Real.log x / (1 - x) + (1 - x) * Real.log (1 - x) / x) / (x * (1 - x)) with hg
  have hin : ∀ x ∈ Ioo (0 : ℝ) 1, IntegrableOn
      (fun w => (Real.log w - Real.log (i9Poly x w 1)) / (x * (1 - x))) (Ioo 0 1) ∧
      ∫ w in Ioo (0 : ℝ) 1, (Real.log w - Real.log (i9Poly x w 1)) / (x * (1 - x)) = g x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have h := i9_Ioo_of_nonpos_cont (F := fun w => (w * Real.log w - w -
        ((x + (1 - x) * w) * Real.log (x + (1 - x) * w) - (x + (1 - x) * w)) / (1 - x) -
        (((1 - x) + x * w) * Real.log ((1 - x) + x * w) - ((1 - x) + x * w)) / x) /
          (x * (1 - x)))
      (f := fun w => (Real.log w - Real.log (i9Poly x w 1)) / (x * (1 - x)))
      (by
        have := Real.continuous_mul_log; have := i9_continuous_mulLog x (1 - x)
        have := i9_continuous_mulLog (1 - x) x
        fun_prop)
      (fun w hw => by
        have hA : 0 < x + (1 - x) * w := by nlinarith [hx.1, hx.2, hw.1, hw.2]
        have hB : 0 < (1 - x) + x * w := by nlinarith [hx.1, hx.2, hw.1, hw.2]
        have h1 := i9_hasDerivAt_mulLog' hw.1
        have h3 := i9_hasDerivAt_mulLog (a := x) (b := 1 - x) (x := w) hA
        have h4 := i9_hasDerivAt_mulLog (a := 1 - x) (b := x) (x := w) hB
        have l3 : HasDerivAt (fun w => x + (1 - x) * w) (1 - x) w := by
          simpa using ((hasDerivAt_id' w).const_mul (1 - x)).const_add x
        have l4 : HasDerivAt (fun w => (1 - x) + x * w) x w := by
          simpa using ((hasDerivAt_id' w).const_mul x).const_add (1 - x)
        refine ((((h1.sub (hasDerivAt_id' w)).sub ((h3.sub l3).div_const (1 - x))).sub
          ((h4.sub l4).div_const x)).div_const (x * (1 - x))).congr_deriv ?_
        rw [log_i9Poly_one' hx hw]
        field_simp
        ring)
      (fun w hw => hf x hx w hw)
    refine ⟨h.1, ?_⟩
    rw [h.2, hg]
    simp
    field_simp
    ring
  have hgn : ∀ x ∈ Ioo (0 : ℝ) 1, g x ≤ 0 := fun x hx => by
    rw [← (hin x hx).2]
    exact setIntegral_nonpos measurableSet_Ioo fun w hw => hf x hx w hw
  have hout := i9_Ioo_of_nonpos (F := i9K1G) (f := g)
    (fun x hx => by
      have hx0 : x ≠ 0 := hx.1.ne'
      have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
      have h2 := i9_hasDerivAt_mulLog (a := 1) (b := -1) (x := x) (by linarith [hx.2])
      have h1 := i9_hasDerivAt_mulLog' hx.1
      have l1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
        simpa using (hasDerivAt_id' x).const_sub 1
      refine ((h2.neg.div (hasDerivAt_id' x) hx0).add (h1.div l1 hx1)).congr_deriv ?_
      simp only [Pi.neg_apply]
      rw [hg]
      field_simp
      ring_nf)
    hgn i9K1G_tendsto_zero i9K1G_tendsto_one
  refine i9_square_nonpos (by unfold i9Poly; fun_prop) hf hin hout.1 ?_
  rw [hout.2]
  norm_num

/-! ### `K₁ = -10` -/

theorem i9K1_alg {c w P Lc Lw LP : ℝ} (hc : c ≠ 0) (hw : w ≠ 0) (hP : P = c * (1 - w) ^ 2 + w) :
    ((2 * Lc + 2 * Lw - 3 * LP) ^ 1 * P - (2 * Lc - Lw) ^ 1 * w - (2 * Lw - Lc) ^ 1 * c) /
        ((Nat.factorial 1 : ℕ) * (c * w)) =
      3 * ((Lc - LP) / w) + 3 * ((Lw - LP) / c) + 3 * ((2 - w) * LP) - 2 * ((2 - w) * Lc) -
        2 * ((2 - w) * Lw) := by
  subst hP
  simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul]
  field_simp
  ring

/-- **`K₁ = -10`**. -/
theorem i9KCoeff_one : i9KCoeff 1 = -10 := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  obtain ⟨i1, v1⟩ := i9K1_piece1
  obtain ⟨i2, v2⟩ := i9K1_piece2
  obtain ⟨i3, v3⟩ := i9K1_piece3
  obtain ⟨i4, v4⟩ := i9K1_piece4
  obtain ⟨i5, v5⟩ := i9K1_piece5
  have h : EqOn (fun z : ℝ × ℝ => i9KCoeffFun 1 z.1 z.2) (fun z =>
      3 * ((Real.log (z.1 * (1 - z.1)) - Real.log (i9Poly z.1 z.2 1)) / z.2) +
      3 * ((Real.log z.2 - Real.log (i9Poly z.1 z.2 1)) / (z.1 * (1 - z.1))) +
      3 * ((2 - z.2) * Real.log (i9Poly z.1 z.2 1)) -
      2 * ((2 - z.2) * Real.log (z.1 * (1 - z.1))) - 2 * ((2 - z.2) * Real.log z.2))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := fun z hz => by
    simp only [i9KCoeffFun, i9KB1, i9KB2, i9KB3]
    exact i9K1_alg (i9_c_pos hz.1).ne' hz.2.1.ne' (by unfold i9Poly; ring)
  rw [i9KCoeff, setIntegral_congr_fun hS h, integral_sub, integral_sub, integral_add,
    integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, v1, v2, v3, v4, v5]
  · ring
  all_goals first
    | exact i1.const_mul 3 | exact i2.const_mul 3 | exact i3.const_mul 3
    | exact i4.const_mul 2 | exact i5.const_mul 2
    | exact (i1.const_mul 3).add (i2.const_mul 3)
    | exact ((i1.const_mul 3).add (i2.const_mul 3)).add (i3.const_mul 3)
    | exact (((i1.const_mul 3).add (i2.const_mul 3)).add (i3.const_mul 3)).sub
        (i4.const_mul 2)

/-- **`K` through `ε³`, given `K₂` and `K₃`**. -/
theorem hasTruncLaurent_i9K_of_coeff23
    (h2 : i9KCoeff 2 = -47 + 31 * Real.pi ^ 2 / 4 + 3 * QED.Polylog.zeta3)
    (h3 : i9KCoeff 3 = -197 + 265 * Real.pi ^ 2 / 6 + 144 * QED.Polylog.zeta3 -
      Real.pi ^ 4 / 12 - 72 * Real.pi ^ 2 * Real.log 2) :
    HasTruncLaurent i9K i9KTarget 4 :=
  hasTruncLaurent_i9K_of_coeff i9KCoeff_one h2 h3

end QED.ThreeLoopD
