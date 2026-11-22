/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Analytic

/-!
# Set (d), master `I₉`: the subtracted representation equals the Feynman integral on a strip

On `0 < re ε < 1/6` (so `s = 1 - 3ε` has `1/2 < re s < 1`) the Feynman-parameter integral
`QED.ThreeLoopD.i9Feyn` converges absolutely, and splitting
`P ^ s = (w y) ^ s + c ^ s + (1 - y) Ψ|_{y=0} + y Ψ|_{y=1} + Ψ_sub` pointwise gives
`QED.ThreeLoopD.i9T ε = QED.ThreeLoopD.i9Feyn ε`: the first three pieces are products of Beta
integrals, the fourth is `B(1 + ε, ε) K(ε)`, and the last is the remainder. Only boundedness of
the five pieces is needed (`‖r ^ s‖ ≤ 2` for `0 ≤ r ≤ 2`), against the integrable weight
`c ^ (2ε - 1) w ^ (2ε - 1) y ^ (ε - 1) (1 - y) ^ (ε - 1)`.

## Main results

* `QED.ThreeLoopD.i9T_eq_i9Feyn`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-! ### Beta integrals on `(0, 1)` -/

theorem i9_betaIntegral_eq (u v : ℂ) :
    betaIntegral u v = ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (u - 1) * ((1 - t : ℝ) : ℂ) ^ (v - 1) := by
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  push_cast; rfl

theorem i9_integrableOn_beta {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (u - 1) * ((1 - t : ℝ) : ℂ) ^ (v - 1)) (Ioo 0 1) := by
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    (betaIntegral_convergent hu hv)
  push_cast; exact h

theorem i9_integral_beta {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (u - 1) * ((1 - t : ℝ) : ℂ) ^ (v - 1) = i9Beta u v := by
  rw [← i9_betaIntegral_eq, betaIntegral_eq_Gamma_mul_div _ _ hu hv, i9Beta]

theorem i9_integrableOn_cpow {u : ℂ} (hu : 0 < u.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (u - 1)) (Ioo 0 1) := by
  have h := i9_integrableOn_beta hu (v := 1) (by norm_num)
  simpa using h

theorem i9_integral_cpow {u : ℂ} (hu : 0 < u.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (u - 1) = 1 / u := by
  have h := i9_betaIntegral_eq u 1
  rw [betaIntegral_eval_one_right hu] at h
  simpa using h.symm

theorem i9_cpow_c {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (a : ℂ) :
    ((x * (1 - x) : ℝ) : ℂ) ^ a = (x : ℂ) ^ a * ((1 - x : ℝ) : ℂ) ^ a := by
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.1.le (by linarith [hx.2])]

theorem i9_integrableOn_cpow_c {u : ℂ} (hu : 0 < u.re) :
    IntegrableOn (fun t : ℝ => ((t * (1 - t) : ℝ) : ℂ) ^ (u - 1)) (Ioo 0 1) :=
  (i9_integrableOn_beta hu hu).congr_fun (fun _ ht => (i9_cpow_c ht _).symm) measurableSet_Ioo

theorem i9_integral_cpow_c {u : ℂ} (hu : 0 < u.re) :
    ∫ t in Ioo (0 : ℝ) 1, ((t * (1 - t) : ℝ) : ℂ) ^ (u - 1) = i9Beta u u := by
  rw [← i9_integral_beta hu hu]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => i9_cpow_c ht _

/-! ### Products over the cube -/

/-- The open unit cube. -/
abbrev i9Cube : Set (ℝ × ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)

theorem i9_measurableSet_cube : MeasurableSet i9Cube :=
  measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)

theorem i9_integral_cube_mul (a b c : ℝ → ℂ) :
    ∫ z in i9Cube, a z.1 * (b z.2.1 * c z.2.2) =
      (∫ t in Ioo (0 : ℝ) 1, a t) * ((∫ t in Ioo (0 : ℝ) 1, b t) * ∫ t in Ioo (0 : ℝ) 1, c t) := by
  rw [volume_restrict_prod3, integral_prod_mul (f := a) (g := fun p : ℝ × ℝ => b p.1 * c p.2),
    integral_prod_mul]

theorem i9_integral_cube_mul2 (g : ℝ × ℝ → ℂ) (c : ℝ → ℂ) :
    ∫ z in i9Cube, g (z.1, z.2.1) * c z.2.2 =
      (∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, g p) * ∫ t in Ioo (0 : ℝ) 1, c t := by
  rw [volume_restrict_prod3, ← Measure.prodAssoc_prod, integral_map_equiv, volume_restrict_prod2,
    ← integral_prod_mul]
  rfl

/-- A bounded measurable function times the weight is integrable over the cube. -/
theorem i9_integrableOn_cube {ε : ℂ} (hε : 0 < ε.re) {F : ℝ × ℝ × ℝ → ℂ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ z ∈ i9Cube, ‖F z‖ ≤ C) :
    IntegrableOn (fun z => i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * F z) i9Cube := by
  have h2 : 0 < (2 * ε).re := by simp; linarith
  have hW : IntegrableOn (fun z : ℝ × ℝ × ℝ => ((z.1 * (1 - z.1) : ℝ) : ℂ) ^ (2 * ε - 1) *
      ((z.2.1 : ℂ) ^ (2 * ε - 1) * i9WtY ε z.2.2)) i9Cube := by
    rw [IntegrableOn, volume_restrict_prod3]
    exact (i9_integrableOn_cpow_c h2).mul_prod ((i9_integrableOn_cpow h2).mul_prod
      (i9_integrableOn_beta hε hε))
  have hb : ∀ᵐ z ∂(volume.restrict i9Cube), ‖F z‖ ≤ C :=
    ae_restrict_of_forall_mem i9_measurableSet_cube hC
  have hm : IntegrableOn _ i9Cube := hW.mul_bdd hF.aestronglyMeasurable hb
  refine hm.congr_fun (fun z _ => ?_) i9_measurableSet_cube
  simp only [i9Wt, i9WtY]; push_cast; ring

/-! ### Bounds on the strip -/

theorem i9_norm_cpow_le_two {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ 2) : ‖(r : ℂ) ^ s‖ ≤ 2 := by
  rcases hr0.eq_or_lt with h | h
  · subst h
    rw [ofReal_zero, zero_cpow (fun h => by simp [h] at hs0)]; simp
  · rw [norm_cpow_eq_rpow_re_of_pos h]
    rcases le_total r 1 with h1 | h1
    · linarith [Real.rpow_le_one h.le h1 hs0.le]
    · calc r ^ s.re ≤ r ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hs1
        _ ≤ 2 := by rw [Real.rpow_one]; exact hr

section Strip

variable {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 6)
include h0 h1

theorem i9_s_re : 0 < (1 - 3 * ε).re ∧ (1 - 3 * ε).re ≤ 1 := by
  simp; constructor <;> linarith

theorem i9_s_ne : 1 - 3 * ε ≠ 0 := fun h => by
  have := (i9_s_re h0 h1).1; rw [h] at this; simp at this

theorem i9_norm_s_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2) : ‖(r : ℂ) ^ (1 - 3 * ε)‖ ≤ 2 :=
  i9_norm_cpow_le_two (i9_s_re h0 h1).1 (i9_s_re h0 h1).2 hr0 hr

theorem i9_norm_psi_le {x w y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : ‖i9Psi ε x w y‖ ≤ 6 := by
  have hc0 := i9_c_nonneg hx
  have hc1 : x * (1 - x) ≤ 2 := (i9_c_le x).trans (by norm_num)
  have hp := i9_norm_s_le h0 h1 (i9Poly_nonneg hx hw hy) (i9Poly_le hx hw hy)
  have hq := i9_norm_s_le h0 h1 (mul_nonneg hw.1 hy.1)
    ((i9_mul_le_one hw.2 hy.1 hy.2).trans (by norm_num))
  have hr := i9_norm_s_le h0 h1 hc0 hc1
  unfold i9Psi
  calc _ ≤ ‖((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε)‖ + ‖((w * y : ℝ) : ℂ) ^ (1 - 3 * ε)‖ +
        ‖((x * (1 - x) : ℝ) : ℂ) ^ (1 - 3 * ε)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ 6 := by linarith

theorem i9_psi_zero {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    i9Psi ε x w 0 = ((x * (1 - x) : ℝ) : ℂ) ^ (1 - 3 * ε) *
      (((1 - w : ℝ) : ℂ) ^ ((3 - 6 * ε) - 1) - 1) := by
  have hw1 : (0 : ℝ) < 1 - w := by linarith [hw.2]
  unfold i9Psi i9Poly
  simp only [mul_zero, add_zero, ofReal_zero, zero_cpow (i9_s_ne h0 h1), sub_zero]
  rw [show (3 - 6 * ε) - 1 = (1 - 3 * ε) + (1 - 3 * ε) by ring,
    cpow_add _ _ (ofReal_ne_zero.mpr hw1.ne'), sq, ofReal_mul (x * (1 - x)),
    mul_cpow_ofReal_nonneg (i9_c_pos hx).le (mul_pos hw1 hw1).le, ofReal_mul (1 - w),
    mul_cpow_ofReal_nonneg hw1.le hw1.le]
  ring

theorem i9_norm_psiSub_le {x w y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : ‖i9PsiSub ε x w y‖ ≤ 18 := by
  have hy0 : ‖(1 - y : ℂ)‖ ≤ 1 := by
    rw [show (1 - y : ℂ) = ((1 - y : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hy1 : ‖(y : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hy.1, hy.2]
  have a := i9_norm_psi_le h0 h1 hx hw hy
  have b := i9_norm_psi_le h0 h1 hx hw (y := 0) (by simp)
  have c := i9_norm_psi_le h0 h1 hx hw (y := 1) (by simp)
  unfold i9PsiSub
  calc _ ≤ ‖i9Psi ε x w y‖ + ‖(1 - y : ℂ)‖ * ‖i9Psi ε x w 0‖ + ‖(y : ℂ)‖ * ‖i9Psi ε x w 1‖ := by
        rw [← norm_mul, ← norm_mul]
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ 6 + 1 * 6 + 1 * 6 := by gcongr
    _ = 18 := by norm_num

theorem i9_integrableOn_psi_pieces :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
        ((z.2.1 * z.2.2 : ℝ) : ℂ) ^ (1 - 3 * ε)) i9Cube ∧
      IntegrableOn (fun z : ℝ × ℝ × ℝ => i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
        ((z.1 * (1 - z.1) : ℝ) : ℂ) ^ (1 - 3 * ε)) i9Cube ∧
      IntegrableOn (fun z : ℝ × ℝ × ℝ => i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
        ((1 - z.2.2 : ℂ) * i9Psi ε z.1 z.2.1 0)) i9Cube ∧
      IntegrableOn (fun z : ℝ × ℝ × ℝ => i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
        ((z.2.2 : ℂ) * i9Psi ε z.1 z.2.1 1)) i9Cube ∧
      IntegrableOn (fun z : ℝ × ℝ × ℝ => i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
        i9PsiSub ε z.1 z.2.1 z.2.2) i9Cube := by
  have hI := fun {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) => i9_mem_Icc ht
  refine ⟨i9_integrableOn_cube h0 (C := 2) (by fun_prop) fun z hz => ?_,
    i9_integrableOn_cube h0 (C := 2) (by fun_prop) fun z hz => ?_,
    i9_integrableOn_cube h0 (C := 6) (by unfold i9Psi i9Poly; fun_prop) fun z hz => ?_,
    i9_integrableOn_cube h0 (C := 6) (by unfold i9Psi i9Poly; fun_prop) fun z hz => ?_,
    i9_integrableOn_cube h0 (C := 18) (by unfold i9PsiSub i9Psi i9Poly; fun_prop)
      fun z hz => i9_norm_psiSub_le h0 h1 (hI hz.1) (hI hz.2.1) (hI hz.2.2)⟩
  · exact i9_norm_s_le h0 h1 (mul_pos hz.2.1.1 hz.2.2.1).le
      ((i9_mul_le_one hz.2.1.2.le hz.2.2.1.le hz.2.2.2.le).trans (by norm_num))
  · exact i9_norm_s_le h0 h1 (i9_c_pos hz.1).le ((i9_c_le _).trans (by norm_num))
  · have hy : ‖(1 - z.2.2 : ℂ)‖ ≤ 1 := by
      rw [show (1 - z.2.2 : ℂ) = ((1 - z.2.2 : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, abs_le]; constructor <;> linarith [hz.2.2.1, hz.2.2.2]
    rw [norm_mul]
    exact (mul_le_mul hy (i9_norm_psi_le h0 h1 (hI hz.1) (hI hz.2.1) (y := 0) (by simp))
      (norm_nonneg _) zero_le_one).trans (by norm_num)
  · have hy : ‖(z.2.2 : ℂ)‖ ≤ 1 := by
      rw [norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hz.2.2.1, hz.2.2.2]
    rw [norm_mul]
    exact (mul_le_mul hy (i9_norm_psi_le h0 h1 (hI hz.1) (hI hz.2.1) (y := 1) (by simp))
      (norm_nonneg _) zero_le_one).trans (by norm_num)

/-- **The continued integral equals the Feynman integral on the strip** `0 < re ε < 1/6`. -/
theorem i9T_eq_i9Feyn : i9T ε = i9Feyn ε := by
  obtain ⟨I1, I2, I3, I4, I5⟩ := i9_integrableOn_psi_pieces h0 h1
  have h2 : 0 < (2 * ε).re := by simp; linarith
  have hm1 : 0 < (1 - ε).re := by simp; linarith
  have hm2 : 0 < (1 - 2 * ε).re := by simp; linarith
  have hp1 : 0 < (1 + ε).re := by simp; linarith
  have hm6 : 0 < (3 - 6 * ε).re := by simp; linarith
  have key : (fun z : ℝ × ℝ × ℝ => i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
      ((i9Poly z.1 z.2.1 z.2.2 : ℝ) : ℂ) ^ (1 - 3 * ε)) = fun z =>
      i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * ((z.2.1 * z.2.2 : ℝ) : ℂ) ^ (1 - 3 * ε) +
      i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * ((z.1 * (1 - z.1) : ℝ) : ℂ) ^ (1 - 3 * ε) +
      i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * ((1 - z.2.2 : ℂ) * i9Psi ε z.1 z.2.1 0) +
      i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * ((z.2.2 : ℂ) * i9Psi ε z.1 z.2.1 1) +
      i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * i9PsiSub ε z.1 z.2.1 z.2.2 := by
    funext z; simp only [i9PsiSub, i9Psi]; ring
  unfold i9Feyn
  rw [key, integral_add ?_ I5, integral_add ?_ I4, integral_add ?_ I3, integral_add I1 I2]
  rotate_left
  · exact I1.add I2
  · exact (I1.add I2).add I3
  · exact ((I1.add I2).add I3).add I4
  have hne : ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 → (t : ℂ) ≠ 0 := fun ht => ofReal_ne_zero.mpr ht.1.ne'
  have hne1 : ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 → ((1 - t : ℝ) : ℂ) ≠ 0 := fun ht =>
    ofReal_ne_zero.mpr (by linarith [ht.2])
  have hcne : ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 → ((t * (1 - t) : ℝ) : ℂ) ≠ 0 := fun ht =>
    ofReal_ne_zero.mpr (i9_c_pos ht).ne'
  -- the piece `(w y) ^ s`
  have e1 : ∫ z in i9Cube, i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
      ((z.2.1 * z.2.2 : ℝ) : ℂ) ^ (1 - 3 * ε) =
      i9Beta (2 * ε) (2 * ε) * (1 / (1 - ε) * i9Beta (1 - 2 * ε) ε) := by
    rw [← i9_integral_cpow_c h2, ← i9_integral_cpow hm1, ← i9_integral_beta hm2 h0,
      ← i9_integral_cube_mul]
    refine setIntegral_congr_fun i9_measurableSet_cube fun z hz => ?_
    simp only [i9Wt, i9WtY]
    rw [ofReal_mul z.2.1, mul_cpow_ofReal_nonneg hz.2.1.1.le hz.2.2.1.le,
      show (1 - ε) - 1 = (2 * ε - 1) + (1 - 3 * ε) by ring, cpow_add _ _ (hne hz.2.1),
      show (1 - 2 * ε) - 1 = (ε - 1) + (1 - 3 * ε) by ring, cpow_add _ _ (hne hz.2.2)]
    ring
  -- the piece `c ^ s`
  have e2 : ∫ z in i9Cube, i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
      ((z.1 * (1 - z.1) : ℝ) : ℂ) ^ (1 - 3 * ε) =
      i9Beta (1 - ε) (1 - ε) * (1 / (2 * ε) * i9Beta ε ε) := by
    rw [← i9_integral_cpow_c hm1, ← i9_integral_cpow h2, ← i9_integral_beta h0 h0,
      ← i9_integral_cube_mul]
    refine setIntegral_congr_fun i9_measurableSet_cube fun z hz => ?_
    simp only [i9Wt, i9WtY]
    rw [show (1 - ε) - 1 = (2 * ε - 1) + (1 - 3 * ε) by ring, cpow_add _ _ (hcne hz.1)]
    ring
  -- the piece `(1 - y) Ψ|_{y=0}`
  have e3 : ∫ z in i9Cube, i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
      ((1 - z.2.2 : ℂ) * i9Psi ε z.1 z.2.1 0) =
      i9Beta (1 - ε) (1 - ε) * ((i9Beta (2 * ε) (3 - 6 * ε) - 1 / (2 * ε)) *
        i9Beta ε (1 + ε)) := by
    have eb : ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (2 * ε - 1) *
        (((1 - t : ℝ) : ℂ) ^ ((3 - 6 * ε) - 1) - 1) =
        i9Beta (2 * ε) (3 - 6 * ε) - 1 / (2 * ε) := by
      simp only [mul_sub, mul_one]
      rw [integral_sub (i9_integrableOn_beta h2 hm6) (i9_integrableOn_cpow h2),
        i9_integral_beta h2 hm6, i9_integral_cpow h2]
    rw [← i9_integral_cpow_c hm1, ← eb, ← i9_integral_beta h0 hp1, ← i9_integral_cube_mul]
    refine setIntegral_congr_fun i9_measurableSet_cube fun z hz => ?_
    simp only [i9Wt, i9WtY]
    rw [i9_psi_zero h0 h1 hz.1 hz.2.1, show (1 - ε) - 1 = (2 * ε - 1) + (1 - 3 * ε) by ring,
      cpow_add _ _ (hcne hz.1), show (1 + ε) - 1 = (ε - 1) + 1 by ring,
      cpow_add _ _ (hne1 hz.2.2), cpow_one]
    push_cast; ring
  -- the piece `y Ψ|_{y=1}`
  have e4 : ∫ z in i9Cube, i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 *
      ((z.2.2 : ℂ) * i9Psi ε z.1 z.2.1 1) = i9K ε * i9Beta (1 + ε) ε := by
    rw [← i9_integral_beta hp1 h0, i9K,
      ← i9_integral_cube_mul2 (fun p => i9Wt ε p.1 p.2 * i9Psi ε p.1 p.2 1)]
    refine setIntegral_congr_fun i9_measurableSet_cube fun z hz => ?_
    simp only [i9WtY]
    rw [show (1 + ε) - 1 = (ε - 1) + 1 by ring, cpow_add _ _ (hne hz.2.2), cpow_one]
    ring
  rw [e1, e2, e3, e4, i9T, i9Closed, i9Rem]
  ring

end Strip

end QED.ThreeLoopD
